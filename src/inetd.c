#define _XOPEN_SOURCE 700

#include <stdbool.h>
#include <unistd.h>
#include <stdlib.h>
#include <stdio.h>
#include <err.h>
#include <string.h>
#include <strings.h>
#include <netdb.h>
#include <sys/types.h>
#include <pwd.h>
#include <sys/wait.h>
#include <sys/socket.h>
#include <sys/select.h>
#include <sys/un.h>
#include <errno.h>
#include <syslog.h>
#include <ctype.h>
#include <fcntl.h>
#include <wordexp.h>
#include <grp.h>

#include "config.h"

/* pipe() fds[2] */
#define PIPE_READ 0
#define PIPE_WRITE 1

/* struct svr_entry */
#define MAX_CONS 10

enum child_state { NEW, CONNECTED, CLOSING, CLOSED };

enum {
    FLAG_WAIT = 0,
    FLAG_NOWAIT = 1,
};

enum {
    FAMILY_INET = 0,
    FAMILY_INET6 = 1,
    FAMILY_UNIX = 2,
};

struct child_entry {
    struct child_entry *next;
    struct svr_entry *svr;

    enum child_state state;

    /* fds */
    int stderr;
    int slave;

    pid_t pid;

    char *host;
};

struct svr_entry {
    struct svr_entry *next;

    char *service_name;
    char *sock_type;
    char *proto;
    char *flag_str;
    char *user;
    char *server_path;
    char *args;

    int address_len; // e.g. sizeof(struct sockaddr_in)

    int master; // master fd

    /* socket(3) */
    int domain;
    int type;
    int protocol;

    int port;

    uid_t uid;
    gid_t gid;

    int flags;

    ssize_t sock_size;
    int family;

    struct child_entry *clients[MAX_CONS];
};

static const struct sock_type_map {
    const char *name;
    int type;
} sock_types[] = {
    { "stream", SOCK_STREAM },
    { "dgram",  SOCK_DGRAM  },
    { NULL, -1 },
};

static const struct {
    int domain;
    size_t sockaddr_size;
} family_info[] = {
    [FAMILY_INET] = { AF_INET, sizeof(struct sockaddr_in) },
    [FAMILY_INET6] = { -1, 0 },
    [FAMILY_UNIX] = { AF_UNIX, sizeof(struct sockaddr_un) },
    { -1, -1 },
};

static const struct {
    const char *const name;
    const int family;
    const int domain;
    const int protocol;
} protocols[] = {
    { "tcp"  , FAMILY_INET , AF_INET , IPPROTO_TCP } , 
    { "udp"  , FAMILY_INET , AF_INET , IPPROTO_UDP } , 
    { "unix" , FAMILY_UNIX , AF_UNIX , PF_UNIX }     , 
    { NULL   , -1          , -1      , -1 }          , 
};

static struct svr_entry *svr_list;
static struct child_entry *child_list;
static const char *const default_config_file = "/etc/inetd.conf";
static bool opt_debug = false;
static const char *opt_config_file = default_config_file;
static bool master_running;

static void show_version(FILE *fp)
{
    fprintf(fp,
            "inetd " VERSION "\n"
            "\n"
            "Written by http://github.com/juur");
}

static void show_usage(FILE *fp)
{
    fprintf(fp,
            "inetd -- the internet \"super-server\"\n"
            "\n"
            "Usage: inetd [-dhv] [-f config file]\n"
            "\n"
            "Options:\n"
            "  -f file   load alternative config file\n"
            "  -h        show help\n"
            "  -v        show version\n"
            "  -d        turn on debugging\n");
}

static void trim(char *str)
{
    char *ptr;

    ptr = str + (strlen(str) - 1);

    while(ptr >= str && isspace(*ptr))
        *ptr-- = '\0';
}

static int getsocktype(const char *name)
{
    int i;

    for (i = 0; sock_types[i].name; i++)
        if (!strcasecmp(name, sock_types[i].name))
            return sock_types[i].type;

    return -1;
}

static void close_socket(int *fd)
{
    shutdown(*fd, SHUT_RDWR);
    close(*fd);
    *fd = -1;
}

static void nonblock(int sock)
{
    int flags = fcntl(sock, F_GETFL, 0);
    flags |= O_NONBLOCK;
    fcntl(sock, F_SETFL, flags);
}

static int parse_flags(const char *flag)
{
    if (!strcasecmp(flag, "wait")) /* do not accept() */
        return FLAG_WAIT;
    else if(!strcasecmp(flag, "nowait")) /* do accept() */
        return FLAG_NOWAIT;

    return -1;
}

static void free_svr_entry(struct svr_entry *entry)
{
    if (entry->master != -1)
        close_socket(&entry->master);

    if (entry->service_name)
        free(entry->service_name);

    if (entry->sock_type)
        free(entry->sock_type);

    if (entry->proto)
        free(entry->proto);

    if (entry->flag_str)
        free(entry->flag_str);

    if (entry->user)
        free(entry->user);

    if (entry->server_path)
        free(entry->server_path);

    if (entry->args)
        free(entry->args);

    free(entry);
}

[[gnu::malloc(free_svr_entry)]] static struct svr_entry *alloc_svr_entry(void)
{
    struct svr_entry *ret;

    if ((ret = calloc(1, sizeof(struct svr_entry))) == NULL)
        return NULL;

    ret->master = -1;
    ret->uid = -1U;
    ret->gid = -1U;

    return ret;
}

static void remove_child(struct child_entry *ent)
{
    struct child_entry *next = NULL;

    if (child_list == ent) {
        child_list = ent->next;
        ent->next = NULL;
        return;
    }

    for (struct child_entry *cur = child_list; cur; cur = next)
    {
        next = cur->next;

        if (next != ent)
            continue;

        cur->next = ent->next;
        ent->next = NULL;

        break;
    }
}

static void add_child(struct child_entry *ent)
{
    ent->next = child_list;
    child_list = ent;
}

static void free_child_entry(struct child_entry *entry)
{
    /* ensure firstly we are CLOSING */
    if (entry->state != CLOSED)
        entry->state = CLOSING;

    /* if the child process is still around, kill it */
    if (entry->pid != -1) {
        pid_t pid = entry->pid;
        kill(pid, SIGKILL);
        /* there is potentially a race here so return */
        if (master_running)
            return;
        waitpid(pid, NULL, 0);
    }

    entry->state = CLOSED;
    syslog(LOG_INFO, "closing child pid %d from %s", entry->pid, entry->host ? entry->host : "<>");

    if (entry->svr) {
        for (int i = 0; i < MAX_CONS; i++)
            if (entry->svr->clients[i] == entry)
                entry->svr->clients[i] = NULL;
        entry->svr = NULL;
    }

    if (entry->stderr != -1) {
        close(entry->stderr);
        entry->stderr = -1;
    }

    if (entry->slave != -1)
        close_socket(&entry->slave);

    if (entry->host) {
        free(entry->host);
        entry->host = NULL;
    }

    remove_child(entry);
    free(entry);
}

[[gnu::malloc(free_child_entry)]] static struct child_entry *alloc_child_entry(void)
{
    struct child_entry *ret;

    if ((ret = calloc(1, sizeof(struct child_entry))) == NULL)
        return NULL;

    return ret;
}

static int validate_entry(struct svr_entry *entry)
{
    entry->domain = -1;

    /* there doesn't seem to a standard way of going from "tcp" to AF_INET + IPPROTO_TCP */
    for (int i = 0; protocols[i].name; i++)
        if (!strcasecmp(protocols[i].name, entry->proto)) {
            entry->domain = protocols[i].domain;
            entry->protocol = protocols[i].protocol;
            entry->sock_size = family_info[protocols[i].family].sockaddr_size;
            entry->family = protocols[i].family;
            break;
        }

    if (entry->domain == -1) {
        warnx("validate_entry: invalid proto <%s>", entry->proto);
        return -1;
    }

    struct servent *servent;
    if ((servent = getservbyname(entry->service_name, entry->proto)) == NULL) {
        warnx("validate_entry: invalid service <%s>", entry->service_name);
        return -1;
    }
    entry->port = servent->s_port;
    free(entry->proto);
    entry->proto = NULL;

    if ((entry->type = getsocktype(entry->sock_type)) == -1) {
        warnx("validate_entry: invalid sock_type <%s>", entry->sock_type);
        return -1;
    }
    free(entry->sock_type);
    entry->sock_type = NULL;

    if ((entry->flags = parse_flags(entry->flag_str)) == -1) {
        warnx("validate_entry: invalid flag <%s>", entry->flag_str);
        return -1;
    }
    free(entry->flag_str);
    entry->flag_str = NULL;

    struct passwd *user;
    if ((user = getpwnam(entry->user)) == NULL) {
        warnx("validate_entry: invalid user <%s>", entry->user);
        return -1;
    }
    entry->uid = user->pw_uid;
    entry->gid = user->pw_gid;
    free(entry->user);
    entry->user = NULL;

    if (access(entry->server_path, X_OK) == -1) {
        warn("validate_entry: access check failed for <%s>", entry->server_path);
        return -1;
    }

    return 0;
}

static int add_entry(const struct svr_entry *extra)
{
    struct svr_entry *ret;

    if ((ret = alloc_svr_entry()) == NULL)
        return -1;

    memcpy(ret, extra, sizeof(struct svr_entry));
    ret->master = -1;

    ret->next = svr_list;
    svr_list = ret;

    return 0;
}

static int parse_config(FILE *cfg)
{
    char *lineptr;
    size_t linelen;
    ssize_t rc;
    int line;
    char *service_name, *sock_type, *proto, *flags, *user, *server_path, *args;
    bool running;

    lineptr = NULL;
    line = -1;
    running = true;

    while (running)
    {
        if (lineptr)
            free(lineptr);

        lineptr = NULL;
        linelen = 0;

        if (ferror(cfg)) {
            running = false;
            continue;
        }

        if (feof(cfg)) {
            running = false;
            continue;
        }

        line++;

        if ((rc = getline(&lineptr, &linelen, cfg)) <= 0) {
            if (feof(cfg)) {
                running = false;
                continue;
            } else if (ferror(cfg)) {
                warnx("parse_config: ferror");
                return -1;
            }
            /* else if (rc == -1) */
            warn("parse_config: getline");
            return -1;
        }

        if (lineptr == NULL)
            continue;

        if (*lineptr == '#')
            continue;

        if (strlen(lineptr) == 0)
            continue;

        service_name = NULL;
        sock_type = NULL;
        proto = NULL;
        flags = NULL;
        user = NULL;
        server_path = NULL;
        args = NULL;

        /* <service_name> <sock_type> <proto> <flags> <user> <server_path> <args> */
        if ((rc = sscanf(lineptr, " %ms %ms %ms %ms %ms %ms %m[^\n]",
                        &service_name,
                        &sock_type,
                        &proto,
                        &flags,
                        &user,
                        &server_path,
                        &args)) < 0) {
            warn("parse_config: sscanf");
            return -1;
        } else if (rc < 6) {
            warnx("parse_config: malformed line %d", line);
            continue;
        }

        struct svr_entry entry = {
            .service_name = service_name,
            .sock_type = sock_type,
            .proto = proto,
            .flag_str = flags,
            .user = user,
            .server_path = server_path,
            .args = args,
        };

        if (validate_entry(&entry) == -1)
            continue;

        if (add_entry(&entry) == -1) {
            warn("parse_config: failed to add_entry");
            continue;
        }
    }

    if (lineptr) {
        free(lineptr);
        lineptr = NULL;
    }

    return 0;
}

static void def_signal_handler(int sig, siginfo_t *si, void *)
{
    switch(sig)
    {
        case SIGINT:
        case SIGTERM:
        case SIGQUIT:
            if (master_running)
                syslog(LOG_NOTICE, "signal received, shutting down");

            master_running = false;
            break;

        case SIGCHLD:
            {
                int wstatus;
                if (waitpid(si->si_pid, &wstatus, WNOHANG) == -1)
                    if (master_running)
                        syslog(LOG_WARNING, "waitpid on %d failed: %s", si->si_pid, strerror(errno));

                for (struct child_entry *ent = child_list; ent; ent = ent->next)
                {
                    if (ent->pid == si->si_pid) {
                        if (ent->state != CLOSED)
                            ent->state = CLOSING;
                        ent->pid = -1;
                    }
                }
            }
            break;

        default:
            syslog(LOG_WARNING, "def_signal_handler: unknown signal %d received.", sig);
            break;
    }
}

/* indicated by POSIX but not defined, this is Linux's defintion */
extern int setgroups(size_t size, const gid_t *);

[[gnu::noreturn]] static void execute_child(const struct sockaddr_storage *, const char *cmd, const char *args)
{
    setsid();

    setgroups(0, NULL);

    setvbuf(stdout, NULL, _IONBF, 0);
    setvbuf(stdin, NULL, _IONBF, 0);
    setvbuf(stderr, NULL, _IONBF, 0);

    int rc;

    wordexp_t we;
    const char *msg;
    size_t num_args = 1;

    if (args) {
        if ((rc = wordexp(args, &we, WRDE_NOCMD|WRDE_UNDEF)) != 0) {
            switch(rc)
            {
                case WRDE_BADCHAR:
                    msg = "WRDE_BADCHAR";
                    break;
                case WRDE_BADVAL:
                    msg = "WRDE_BADVAL";
                    break;
                case WRDE_CMDSUB:
                    msg = "WRDE_CMDSUB";
                    break;
                case WRDE_NOSPACE:
                    msg = "WRDE_NOSPACE";
                    break;
                case WRDE_SYNTAX:
                    msg = "WRDE_SYNTAX";
                    break;
                default:
                    msg = "WRDE_UNKNOWN";
                    break;
            }
            syslog(LOG_WARNING, "execute_child: word expansion failed: %s", msg);
            rc = EXIT_FAILURE;
            goto finish;
        }
        num_args += we.we_wordc;
    }

    char *envp[] = {
        "SHLVL=1",
        "HOME=/",
        "PATH=/bin:/usr/bin",
        NULL
    };

    char **argv;

    if ((argv = calloc(num_args + 1, sizeof(char *))) == NULL) {
        syslog(LOG_ERR, "execute_child: calloc: %s", strerror(errno));
        rc = EXIT_FAILURE;
        goto finish;
    }

    if (args)
        memcpy(&argv[1], we.we_wordv, sizeof(char *) * we.we_wordc);
    argv[0] = (char *)cmd;

    rc = execve(cmd, argv, envp);

    if (rc == -1) {
        syslog(LOG_ERR, "execute_child: system: %s", strerror(errno));
    } else if (rc == 127) {
        syslog(LOG_ERR, "execute_child: system was 127");
    }

    rc = EXIT_FAILURE;

    /* don't invoke atexit() */
finish:
    _exit(rc);
}

static void check_children(void)
{
    struct child_entry *next;

    for (struct child_entry *ent = child_list; ent; ent = next)
    {
        next = ent->next;

        switch (ent->state)
        {
            case CLOSING:
            case CLOSED:
                free_child_entry(ent);
                break;
            default:
                break;
        }
    }
}

/* TODO proper clean up */

static void clean_entries(void)
{
    for (struct child_entry *next = NULL, *ent = child_list; ent; ent = next)
    {
        next = ent->next;
        free_child_entry(ent);
    }

    for (struct svr_entry *next = NULL, *ent = svr_list; ent; ent = next)
    {
        next = ent->next;
        free_svr_entry(ent);
    }
}

static void clean_syslog(void)
{
    closelog();
}

static void main_loop(void)
{
    while (master_running)
    {
        int max_fd = 0;

        fd_set in;

        FD_ZERO(&in);

        for (const struct svr_entry *ent = svr_list; ent; ent = ent->next)
        {
            if (ent->master == -1)
                continue;

            if (ent->master != -1) {
                if (ent->master > max_fd)
                    max_fd = ent->master;
                FD_SET(ent->master, &in);
            }
        }

        for (const struct child_entry *ent = child_list; ent; ent = ent->next)
        {
            if (ent->state != CONNECTED)
                continue;

            if (ent->slave != -1) {
                if (ent->slave > max_fd)
                    max_fd = ent->slave;
                FD_SET(ent->slave, &in);
            }

            if (ent->stderr != -1) {
                if (ent->stderr > max_fd)
                    max_fd = ent->stderr;
                FD_SET(ent->stderr, &in);
            }
        }

        int rc;

        struct timeval timeout;

        timeout.tv_sec = 0;
        timeout.tv_usec = 10000;

        rc = select(max_fd + 1, &in, NULL, NULL, &timeout);

        if (rc == -1 && errno == EINTR) {
            continue;
        } else if (rc == -1) {
            syslog(LOG_WARNING, "main_loop: select: %s", strerror(errno));
            continue;
        } else if (rc == 0) {
            check_children();
            continue;
        }

        char buf[BUFSIZ] = {0};

        for (struct child_entry *ent = child_list; ent; ent = ent->next)
        {
            if (ent->state != CONNECTED)
                continue;

            if (ent->stderr != -1 && FD_ISSET(ent->stderr, &in)) {

                if ((rc = read(ent->stderr, buf, BUFSIZ)) == -1) {
                    if (errno == EBADF)
                        ent->stderr = -1;
                    else
                        syslog(LOG_WARNING, "read: stderr[%d]: %s", ent->stderr, strerror(errno));
                } else if (rc > 0) {
                    trim(buf);
                    syslog(LOG_WARNING, "stderr from child: %s", buf);
                } else {
                    close(ent->stderr);
                    ent->stderr = -1;
                }
            }

            if (ent->slave != -1 && FD_ISSET(ent->slave, &in)) {
                /* ??? */
            }
        }


        for (struct svr_entry *ent = svr_list; ent; ent=ent->next)
        {
            /* TODO support SOCK_DGRAM */
            if (ent->type != SOCK_STREAM)
                continue;

            if (ent->master != -1 && FD_ISSET(ent->master, &in)) {
                char buf[BUFSIZ];
                struct sockaddr_storage storage;
                socklen_t storage_len;
                int new_fd, offset = -1;
                pid_t child_pid;
                struct child_entry *child_ent;
                int filedes[2];

                storage_len = ent->sock_size;

                /* TODO only apply this to FLAG_NOWAIT */
                if ((new_fd = accept(ent->master, (struct sockaddr *)&storage, &storage_len)) == -1) {
                    syslog(LOG_WARNING, "accept failed: %s", strerror(errno));
                    continue;
                }

                if ((rc = getnameinfo((struct sockaddr *)&storage, storage_len, buf, sizeof(buf), NULL, 0, NI_NUMERICHOST))) {
                    syslog(LOG_WARNING, "getnameinfo failed: %s", gai_strerror(rc));
                    snprintf(buf, sizeof(buf), "UNKNOWN");
                }

                syslog(LOG_INFO, "new connection from %s on fd %d\n", buf, new_fd);

                for (int i = 0; i < MAX_CONS; i++)
                    if (ent->clients[i] == NULL) {
                        offset = i;
                        break;
                    }

                if (offset == -1) {
                    syslog(LOG_WARNING, "too many connections for service %s", ent->service_name);
fail_close_socket:
                    close_socket(&new_fd);
                    continue;
                }

                if ((ent->clients[offset] = child_ent = alloc_child_entry()) == NULL) {
                    syslog(LOG_WARNING, "unable to allocate child: %s", strerror(errno));
                    goto fail_close_socket;
                }
                add_child(child_ent);
                child_ent->slave = new_fd;

                if ((child_ent->host = strdup(buf)) == NULL) {
                    syslog(LOG_WARNING, "unable to allocate memory for hostname: %s", strerror(errno));
                    goto close_child;
                }

                if (pipe(filedes) == -1)
                    goto close_child;

                child_ent->stderr = filedes[PIPE_READ];
                nonblock(child_ent->stderr);

                if ((child_ent->pid = child_pid = fork()) == 0) {
                    close(filedes[PIPE_READ]);
                    ent->master = -1;

                    if (ent->gid != -1U)
                        if (setgid(ent->gid) == -1) {
                            syslog(LOG_ERR, "unable to setgid: %s", strerror(errno));
                            goto close_child;
                        }
                    if (ent->uid != -1U) {
                        setuid(ent->uid); 
                        syslog(LOG_ERR, "unable to setuid: %s", strerror(errno));
                        goto close_child;
                    }

                    /* replace stdin, stdout and stderr */
                    dup2(new_fd, STDIN_FILENO);
                    dup2(new_fd, STDOUT_FILENO);
                    dup2(filedes[PIPE_WRITE], STDERR_FILENO);

                    execute_child(&storage, ent->server_path, ent->args);
                }

                close(filedes[PIPE_WRITE]);

                if (child_pid == -1)
                    goto close_child;

                child_ent->state = CONNECTED;
                continue;

close_child:
                child_ent->state = CLOSING;
            }
        }
    }
}
static void setup_servers(void)
{
    for (struct svr_entry *ent = svr_list; ent; ent=ent->next)
    {
        if ((ent->master = socket(ent->domain, ent->type, ent->protocol)) == -1) {
            syslog(LOG_ERR, "unable to create socket for %s: %s", ent->service_name, strerror(errno));
            continue;
        }

        struct linger linger = {
            .l_onoff = 0,
            .l_linger = 0,
        };

        if (setsockopt(ent->master, SOL_SOCKET, SO_LINGER, &linger, sizeof(linger)) == -1)
            syslog(LOG_WARNING, "setsockopt(SO_LINGER): %s", strerror(errno));

        int reuseaddr = 1;
        if (setsockopt(ent->master, SOL_SOCKET, SO_REUSEADDR, &reuseaddr, sizeof(reuseaddr)) == -1)
            syslog(LOG_WARNING, "setsockopt(SO_REUSEADDR): %s", strerror(errno));

        struct sockaddr *address;
        socklen_t address_len;

        switch (ent->domain) {
            case AF_INET:
                {
                    struct sockaddr_in sin;
                    sin.sin_family = AF_INET;
                    sin.sin_addr.s_addr = INADDR_ANY;
                    sin.sin_port = ent->port;
                    address = (struct sockaddr *)&sin;
                    ent->address_len = address_len = sizeof(sin);
                }
                break;
            default:
                syslog(LOG_ERR, "domain %d not implemented", ent->domain);
                continue;
        }

        if (bind(ent->master, address, address_len) == -1) {
            syslog(LOG_ERR, "unable to bind service %s: %s", ent->service_name, strerror(errno));
            close_socket(&ent->master);
            continue;
        }

        if (listen(ent->master, 10) == -1) {
            syslog(LOG_ERR, "unable to listen for service %s: %s", ent->service_name, strerror(errno));
            close_socket(&ent->master);
            continue;
        }

        syslog(LOG_INFO, "listening for service %s", ent->service_name);
    }
}


int main(int argc, char *argv[])
{
    svr_list = NULL;
    child_list = NULL;

    setvbuf(stdout, NULL, _IONBF, 0);
    setvbuf(stdin, NULL, _IONBF, 0);
    setvbuf(stderr, NULL, _IONBF, 0);

    {
        int opt;

        while ((opt = getopt(argc, argv, "dvhf:")) != -1)
        {
            switch (opt) {
                case 'd':
                    opt_debug = true;
                    break;
                case 'v':
                    show_version(stdout);
                    exit(EXIT_SUCCESS);
                case 'h':
                    show_usage(stdout);
                    exit(EXIT_SUCCESS);
                case 'f':
                    opt_config_file = optarg;
                    break;
                default:
                    show_usage(stderr);
                    exit(EXIT_FAILURE);
            }
        }
    }

    atexit(clean_entries);

    FILE *cfg;

    if ((cfg = fopen(opt_config_file, "r")) == NULL)
        err(EXIT_FAILURE, "main: fopen: unable to open <%s>", opt_config_file);

    if (parse_config(cfg) == -1)
        exit(EXIT_FAILURE);

    fclose(cfg);

    openlog("inetd", LOG_PERROR|LOG_PID, LOG_DAEMON);
    atexit(clean_syslog);

    setup_servers();

    struct sigaction def_act = { 0 };

    def_act.sa_sigaction = &def_signal_handler;
    def_act.sa_flags = SA_SIGINFO;

    sigaction(SIGCHLD, &def_act, NULL);
    sigaction(SIGINT, &def_act, NULL);
    sigaction(SIGTERM, &def_act, NULL);
    sigaction(SIGQUIT, &def_act, NULL);

    master_running = true;
    main_loop();

    exit(EXIT_SUCCESS);
}
