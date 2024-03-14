/*
 * apps/s_socket.c - socket-related functions used by s_client and s_server
 */
/* Copyright (C) 1995-1998 Eric Young (eay@cryptsoft.com)
 * All rights reserved.
 *
 * This package is an SSL implementation written
 * by Eric Young (eay@cryptsoft.com).
 * The implementation was written so as to conform with Netscapes SSL.
 *
 * This library is free for commercial and non-commercial use as long as
 * the following conditions are aheared to.  The following conditions
 * apply to all code found in this distribution, be it the RC4, RSA,
 * lhash, DES, etc., code; not just the SSL code.  The SSL documentation
 * included with this distribution is covered by the same copyright terms
 * except that the holder is Tim Hudson (tjh@cryptsoft.com).
 *
 * Copyright remains Eric Young's, and as such any Copyright notices in
 * the code are not to be removed.
 * If this package is used in a product, Eric Young should be given attribution
 * as the author of the parts of the library used.
 * This can be in the form of a textual message at program startup or
 * in documentation (online or textual) provided with the package.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. All advertising materials mentioning features or use of this software
 *    must display the following acknowledgement:
 *    "This product includes cryptographic software written by
 *     Eric Young (eay@cryptsoft.com)"
 *    The word 'cryptographic' can be left out if the rouines from the library
 *    being used are not cryptographic related :-).
 * 4. If you include any Windows specific code (or a derivative thereof) from
 *    the apps directory (application code) you must include an acknowledgement:
 *    "This product includes software written by Tim Hudson (tjh@cryptsoft.com)"
 *
 * THIS SOFTWARE IS PROVIDED BY ERIC YOUNG ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * The licence and distribution terms for any publically available version or
 * derivative of this code cannot be changed.  i.e. this code cannot simply be
 * copied and put under another distribution licence
 * [including the GNU Public Licence.]
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <signal.h>

#ifdef FLAT_INC
# include "e_os2.h"
#else
# include "../e_os2.h"
#endif

/*
 * With IPv6, it looks like Digital has mixed up the proper order of
 * recursive header file inclusion, resulting in the compiler complaining
 * that u_int isn't defined, but only if _POSIX_C_SOURCE is defined, which is
 * needed to have fileno() declared correctly...  So let's define u_int
 */
#if defined(OPENSSL_SYS_VMS_DECC) && !defined(__U_INT)
# define __U_INT
typedef unsigned int u_int;
#endif

#define USE_SOCKETS
#define NON_MAIN
#include "apps.h"
#undef USE_SOCKETS
#undef NON_MAIN
#include "s_apps.h"
#include <openssl/ssl.h>

#ifdef FLAT_INC
# include "e_os.h"
#else
# include "../e_os.h"
#endif

#ifndef OPENSSL_NO_SOCK

# if defined(OPENSSL_SYS_NETWARE) && defined(NETWARE_BSDSOCK)
#  include "netdb.h"
# endif

static struct hostent *GetHostByName(char *name);
# if defined(OPENSSL_SYS_WINDOWS) || (defined(OPENSSL_SYS_NETWARE) && !defined(NETWARE_BSDSOCK))
static void ssl_sock_cleanup(void);
# endif
static int ssl_sock_init(void);
static int init_server(int *sock, char *port, int type);
static int do_accept(int acc_sock, int *sock, char **host);
static int host_ip(char *str, unsigned char ip[4]);

# ifdef OPENSSL_SYS_WIN16
#  define SOCKET_PROTOCOL 0     /* more microsoft stupidity */
# else
#  define SOCKET_PROTOCOL IPPROTO_TCP
# endif

# if defined(OPENSSL_SYS_NETWARE) && !defined(NETWARE_BSDSOCK)
static int wsa_init_done = 0;
# endif

# ifdef OPENSSL_SYS_WINDOWS
static struct WSAData wsa_state;
static int wsa_init_done = 0;

#  ifdef OPENSSL_SYS_WIN16
static HWND topWnd = 0;
static FARPROC lpTopWndProc = NULL;
static FARPROC lpTopHookProc = NULL;
extern HINSTANCE _hInstance;    /* nice global CRT provides */

static LONG FAR PASCAL topHookProc(HWND hwnd, UINT message, WPARAM wParam,
                                   LPARAM lParam)
{
    if (hwnd == topWnd) {
        switch (message) {
        case WM_DESTROY:
        case WM_CLOSE:
            SetWindowLong(topWnd, GWL_WNDPROC, (LONG) lpTopWndProc);
            ssl_sock_cleanup();
            break;
        }
    }
    return CallWindowProc(lpTopWndProc, hwnd, message, wParam, lParam);
}

static BOOL CALLBACK enumproc(HWND hwnd, LPARAM lParam)
{
    topWnd = hwnd;
    return (FALSE);
}

#  endif                        /* OPENSSL_SYS_WIN32 */
# endif                         /* OPENSSL_SYS_WINDOWS */

# ifdef OPENSSL_SYS_WINDOWS
static void ssl_sock_cleanup(void)
{
    if (wsa_init_done) {
        wsa_init_done = 0;
#  ifndef OPENSSL_SYS_WINCE
        WSACancelBlockingCall();
#  endif
        WSACleanup();
    }
}
# elif defined(OPENSSL_SYS_NETWARE) && !defined(NETWARE_BSDSOCK)
static void sock_cleanup(void)
{
    if (wsa_init_done) {
        wsa_init_done = 0;
        WSACleanup();
    }
}
# endif

static int ssl_sock_init(void)
{
# ifdef WATT32
    extern int _watt_do_exit;
    _watt_do_exit = 0;
    if (sock_init())
        return (0);
# elif defined(OPENSSL_SYS_WINDOWS)
    if (!wsa_init_done) {
        int err;

#  ifdef SIGINT
        signal(SIGINT, (void (*)(int))ssl_sock_cleanup);
#  endif
        wsa_init_done = 1;
        memset(&wsa_state, 0, sizeof(wsa_state));
        if (WSAStartup(0x0101, &wsa_state) != 0) {
            err = WSAGetLastError();
            BIO_printf(bio_err, "unable to start WINSOCK, error code=%d\n",
                       err);
            return (0);
        }
#  ifdef OPENSSL_SYS_WIN16
        EnumTaskWindows(GetCurrentTask(), enumproc, 0L);
        lpTopWndProc = (FARPROC) GetWindowLong(topWnd, GWL_WNDPROC);
        lpTopHookProc = MakeProcInstance((FARPROC) topHookProc, _hInstance);

        SetWindowLong(topWnd, GWL_WNDPROC, (LONG) lpTopHookProc);
#  endif                        /* OPENSSL_SYS_WIN16 */
    }
# elif defined(OPENSSL_SYS_NETWARE) && !defined(NETWARE_BSDSOCK)
    WORD wVerReq;
    WSADATA wsaData;
    int err;

    if (!wsa_init_done) {

#  ifdef SIGINT
        signal(SIGINT, (void (*)(int))sock_cleanup);
#  endif

        wsa_init_done = 1;
        wVerReq = MAKEWORD(2, 0);
        err = WSAStartup(wVerReq, &wsaData);
        if (err != 0) {
            BIO_printf(bio_err, "unable to start WINSOCK2, error code=%d\n",
                       err);
            return (0);
        }
    }
# endif                         /* OPENSSL_SYS_WINDOWS */
    return (1);
}

int init_client(int *sock, char *host, char *port, int type)
{
    struct addrinfo *res, *res0, hints;
    char *failed_call = NULL;
    int s;
    int e;

    if (!ssl_sock_init())
        return (0);

    memset(&hints, '\0', sizeof(hints));
    hints.ai_socktype = type;
    hints.ai_flags = AI_ADDRCONFIG;

    e = getaddrinfo(host, port, &hints, &res);
    if (e) {
        fprintf(stderr, "getaddrinfo: %s\n", gai_strerror(e));
        if (e == EAI_SYSTEM)
            perror("getaddrinfo");
        return (0);
    }

    res0 = res;
    while (res) {
        s = socket(res->ai_family, res->ai_socktype, res->ai_protocol);
        if (s == INVALID_SOCKET) {
            failed_call = "socket";
            goto nextres;
        }
# if defined(SO_KEEPALIVE) && !defined(OPENSSL_SYS_MPE)
        if (type == SOCK_STREAM) {
            int i = 0;
            i = setsockopt(s, SOL_SOCKET, SO_KEEPALIVE,
                           (char *)&i, sizeof(i));
            if (i < 0) {
                failed_call = "keepalive";
                goto nextres;
            }
        }
# endif
        if (connect(s, (struct sockaddr *)res->ai_addr, res->ai_addrlen) == 0) {
            freeaddrinfo(res0);
            *sock = s;
            return (1);
        }

        failed_call = "socket";
 nextres:
        if (s != INVALID_SOCKET)
            close(s);
        res = res->ai_next;
    }
    freeaddrinfo(res0);
    closesocket(s);

    perror(failed_call);
    return (0);
}

int do_server(char *port, int type, int *ret,
              int (*cb) (char *hostname, int s, int stype,
                         unsigned char *context), unsigned char *context,
              int naccept)
{
    int sock;
    char *name = NULL;
    int accept_socket = 0;
    int i;

    if (!init_server(&accept_socket, port, type))
        return (0);

    if (ret != NULL) {
        *ret = accept_socket;
        /* return(1); */
    }
    for (;;) {
        if (type == SOCK_STREAM) {
            if (do_accept(accept_socket, &sock, &name) == 0) {
                SHUTDOWN(accept_socket);
                return (0);
            }
        } else
            sock = accept_socket;
        i = (*cb) (name, sock, type, context);
        if (name != NULL)
            OPENSSL_free(name);
        if (type == SOCK_STREAM)
            SHUTDOWN2(sock);
        if (naccept != -1)
            naccept--;
        if (i < 0 || naccept == 0) {
            SHUTDOWN2(accept_socket);
            return (i);
        }
    }
}

static int init_server(int *sock, char *port, int type)
{
    struct addrinfo *res, *res0 = NULL, hints;
    char *failed_call = NULL;
    int s = INVALID_SOCKET;
    int e;

    if (!ssl_sock_init())
        return (0);

    memset(&hints, '\0', sizeof(hints));
    hints.ai_family = AF_INET6;
 tryipv4:
    hints.ai_socktype = type;
    hints.ai_flags = AI_PASSIVE;

    e = getaddrinfo(NULL, port, &hints, &res);
    if (e) {
        if (hints.ai_family == AF_INET) {
            fprintf(stderr, "getaddrinfo: %s\n", gai_strerror(e));
            if (e == EAI_SYSTEM)
                perror("getaddrinfo");
            return (0);
        } else
            res = NULL;
    }

    res0 = res;
    while (res) {
        s = socket(res->ai_family, res->ai_socktype, res->ai_protocol);
        if (s == INVALID_SOCKET) {
            failed_call = "socket";
            goto nextres;
        }
        if (hints.ai_family == AF_INET6) {
            int j = 0;
            setsockopt(s, IPPROTO_IPV6, IPV6_V6ONLY, (void *)&j, sizeof j);
        }
# if defined SOL_SOCKET && defined SO_REUSEADDR
        {
            int j = 1;
            setsockopt(s, SOL_SOCKET, SO_REUSEADDR, (void *)&j, sizeof j);
        }
# endif

        if (bind(s, (struct sockaddr *)res->ai_addr, res->ai_addrlen) == -1) {
            failed_call = "bind";
            goto nextres;
        }
        if (type == SOCK_STREAM && listen(s, 128) == -1) {
            failed_call = "listen";
            goto nextres;
        }

        *sock = s;
        return (1);

 nextres:
        if (s != INVALID_SOCKET)
            close(s);
        res = res->ai_next;
    }
    if (res0)
        freeaddrinfo(res0);

    if (s == INVALID_SOCKET) {
        if (hints.ai_family == AF_INET6) {
            hints.ai_family = AF_INET;
            goto tryipv4;
        }
        perror("socket");
        return (0);
    }

    perror(failed_call);
    return (0);
}

static int do_accept(int acc_sock, int *sock, char **host)
{
    static struct sockaddr_storage from;
    char buffer[NI_MAXHOST];
    int ret;
    int len;
/*      struct linger ling; */

    if (!ssl_sock_init())
        return (0);

# ifndef OPENSSL_SYS_WINDOWS
 redoit:
# endif

    memset((char *)&from, 0, sizeof(from));
    len = sizeof(from);
    /*
     * Note: under VMS with SOCKETSHR the fourth parameter is currently of
     * type (int *) whereas under other systems it is (void *) if you don't
     * have a cast it will choke the compiler: if you do have a cast then you
     * can either go for (int *) or (void *).
     */
    ret = accept(acc_sock, (struct sockaddr *)&from, (void *)&len);
    if (ret == INVALID_SOCKET) {
# if defined(OPENSSL_SYS_WINDOWS) || (defined(OPENSSL_SYS_NETWARE) && !defined(NETWARE_BSDSOCK))
        int i;
        i = WSAGetLastError();
        BIO_printf(bio_err, "accept error %d\n", i);
# else
        if (errno == EINTR) {
            /*
             * check_timeout();
             */
            goto redoit;
        }
        fprintf(stderr, "errno=%d ", errno);
        perror("accept");
# endif
        return (0);
    }

/*-
    ling.l_onoff=1;
    ling.l_linger=0;
    i=setsockopt(ret,SOL_SOCKET,SO_LINGER,(char *)&ling,sizeof(ling));
    if (i < 0) { closesocket(ret); perror("linger"); return(0); }
    i=0;
    i=setsockopt(ret,SOL_SOCKET,SO_KEEPALIVE,(char *)&i,sizeof(i));
    if (i < 0) { closesocket(ret); perror("keepalive"); return(0); }
*/

    if (host == NULL)
        goto end;

    if (getnameinfo((struct sockaddr *)&from, sizeof(from),
                    buffer, sizeof(buffer), NULL, 0, 0)) {
        BIO_printf(bio_err, "getnameinfo failed\n");
        *host = NULL;
        /* return(0); */
    } else {
        if ((*host = (char *)OPENSSL_malloc(strlen(buffer) + 1)) == NULL) {
            perror("OPENSSL_malloc");
            closesocket(ret);
            return (0);
        }
        strcpy(*host, buffer);
    }
 end:
    *sock = ret;
    return (1);
}

int extract_host_port(char *str, char **host_ptr, char **port_ptr)
{
    char *h, *p, *x;

    x = h = str;
    if (*h == '[') {
        h++;
        p = strchr(h, ']');
        if (p == NULL) {
            BIO_printf(bio_err, "no ending bracket for IPv6 address\n");
            return (0);
        }
        *(p++) = '\0';
        x = p;
    }
    p = strchr(x, ':');
    if (p == NULL) {
        BIO_printf(bio_err, "no port defined\n");
        return (0);
    }
    *(p++) = '\0';

    if (host_ptr != NULL)
        *host_ptr = h;
    if (port_ptr != NULL)
        *port_ptr = p;

    return (1);
}

# define GHBN_NUM        4
static struct ghbn_cache_st {
    char name[128];
    struct hostent ent;
    unsigned long order;
} ghbn_cache[GHBN_NUM];

static unsigned long ghbn_hits = 0L;
static unsigned long ghbn_miss = 0L;

static struct hostent *GetHostByName(char *name)
{
    struct hostent *ret;
    int i, lowi = 0;
    unsigned long low = (unsigned long)-1;

    for (i = 0; i < GHBN_NUM; i++) {
        if (low > ghbn_cache[i].order) {
            low = ghbn_cache[i].order;
            lowi = i;
        }
        if (ghbn_cache[i].order > 0) {
            if (strncmp(name, ghbn_cache[i].name, 128) == 0)
                break;
        }
    }
    if (i == GHBN_NUM) {        /* no hit */
        ghbn_miss++;
        ret = gethostbyname(name);
        if (ret == NULL)
            return (NULL);
        /* else add to cache */
        if (strlen(name) < sizeof ghbn_cache[0].name) {
            strcpy(ghbn_cache[lowi].name, name);
            memcpy((char *)&(ghbn_cache[lowi].ent), ret,
                   sizeof(struct hostent));
            ghbn_cache[lowi].order = ghbn_miss + ghbn_hits;
        }
        return (ret);
    } else {
        ghbn_hits++;
        ret = &(ghbn_cache[i].ent);
        ghbn_cache[i].order = ghbn_miss + ghbn_hits;
        return (ret);
    }
}

#endif
