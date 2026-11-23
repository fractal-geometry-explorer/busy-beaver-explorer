/* The front of the counter model of 1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB--- in closed form (23 November 2026).
 *
 * Lifetime model (py/front.py has the derivation and the tests). A group with q groups to its right and size n has
 * lifetime l = n / 3^q rounds. Inside a round, time t runs from 0 to 1 and
 *   - every group loses 1 per unit of t, the front block (n0) gains 1;
 *   - when group j reaches 0 at time t it is removed with its right neighbour, the left neighbour becomes
 *     9 l_(j-1) + l_(j+1), and every lifetime left of it (the front block too) is multiplied by 9;
 *   - at t = 1 the front block becomes the newborn group and a new front block starts at 0.
 * This ignores terms of relative size 3^-q, except the one that is amplified: in the two-round cycle
 * [1, c, X, ...] the aged newborn has exact size c, and the next one has 8c + 8 (the "chain"). The chain is kept
 * exactly as (c0, k): c = (c0 + 8/7) 8^k - 8/7, its lifetime c / 3^q computed in quad precision.
 *
 * Times are absolute death times D = tau + l in fixed point (256 bits, 2^-128). A group whose remaining lifetime exceeds 2^59
 * rounds is "frozen" (it cannot run out before the horizon); runs of frozen groups are one node with a count.
 * The two-round cycle is skipped K cycles at a time (X gains 7 per cycle, everything else loses 2).
 * Events at the right end of the list (from py/rightpart.py, exact) enter as "global" events: at time t of their
 * round, two groups disappear at the right end and every lifetime is multiplied by 9.
 *
 * Input (text, stdin): see py/front.py (write_input). Output: dumps of the front at requested rounds and at the end.
 * gcc -O2 -o front front.c -lquadmath
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <quadmath.h>

/* 256-bit two's complement fixed point, 128 fraction bits */
typedef struct { uint64_t w[4]; } fx;
#define FRAC 128
static fx fx_int(int64_t a) { fx r; uint64_t s = a < 0 ? ~0ULL : 0; r.w[0] = 0; r.w[1] = 0; r.w[2] = (uint64_t)a; r.w[3] = s; return r; }
static fx fx_add(fx a, fx b) { fx r; unsigned __int128 c = 0; for (int i = 0; i < 4; i++) { c += (unsigned __int128)a.w[i] + b.w[i]; r.w[i] = (uint64_t)c; c >>= 64; } return r; }
static fx fx_neg(fx a) { fx r; unsigned __int128 c = 1; for (int i = 0; i < 4; i++) { c += (unsigned __int128)(~a.w[i]); r.w[i] = (uint64_t)c; c >>= 64; } return r; }
static fx fx_sub(fx a, fx b) { return fx_add(a, fx_neg(b)); }
static fx fx_mulu(fx a, uint64_t k) {     /* a * k, a >= 0 */
    fx r; unsigned __int128 c = 0; for (int i = 0; i < 4; i++) { c += (unsigned __int128)a.w[i] * k; r.w[i] = (uint64_t)c; c >>= 64; } return r; }
static int fx_cmp(fx a, fx b) {
    if ((int64_t)a.w[3] != (int64_t)b.w[3]) return (int64_t)a.w[3] < (int64_t)b.w[3] ? -1 : 1;
    for (int i = 2; i >= 0; i--) if (a.w[i] != b.w[i]) return a.w[i] < b.w[i] ? -1 : 1;
    return 0; }
static int fx_eq(fx a, fx b) { return fx_cmp(a, b) == 0; }
static fx INFV;
static fx ONEV;
static fx FREEZEV;
#define ONE ONEV
#define INF INFV
#define FREEZE FREEZEV
static int64_t fx_floor_int(fx a) { return (int64_t)a.w[2]; }   /* for 0 <= a < 2^191 with integer part < 2^63 */
static fx fx_shr1(fx a) { fx r; for (int i = 0; i < 3; i++) r.w[i] = (a.w[i] >> 1) | (a.w[i + 1] << 63); r.w[3] = (uint64_t)((int64_t)a.w[3] >> 1); return r; }
static fx fx_mul9(fx a) { /* signed */ fx r = a; for (int i = 0; i < 3; i++) r = fx_add(r, r); return fx_add(r, a); }
static fx fx_from_q(__float128 x) {     /* 0 <= x < 2^60, x * 2^128 */
    fx r; memset(&r, 0, sizeof r);
    __float128 y = x;
    for (int i = 2; i >= 0; i--) {         /* word i holds bits 64(i-2)+128 ... */
        __float128 scale = ldexpq(1.0Q, 64 * (i - 2));
        __float128 d = floorq(y / scale);
        if (d < 0) d = 0;
        r.w[i] = (uint64_t)d; y -= d * scale; }
    return r; }

typedef struct {
    fx D;            /* absolute death time; INF for frozen */
    int64_t cnt;     /* number of groups (frozen runs) */
    int64_t prev, next;
    int64_t hpos;
    int64_t c0, k;   /* chain, if haschain */
    char haschain, charged;
} Node;

static Node *N;
static int64_t ncap, nused, nfree = -1, head = -1, tail = -1;
static int64_t *H, hn, hcap;
static int64_t m_total;          /* number of groups in the list */
static int64_t tau;              /* current round start (relative) */
static __float128 LOG3;

static void die(const char *s) { fprintf(stderr, "FATAL %s at tau %lld\n", s, (long long)tau); printf("FATAL %s at tau %lld\n", s, (long long)tau); fflush(stdout); exit(2); }

static int64_t newnode(void) {
    int64_t i;
    if (nfree >= 0) { i = nfree; nfree = N[i].next; }
    else {
        if (nused == ncap) { ncap = ncap ? 2 * ncap : 1 << 16; N = realloc(N, ncap * sizeof(Node)); if (!N) die("oom"); }
        i = nused++;
    }
    memset(&N[i], 0, sizeof(Node));
    N[i].prev = N[i].next = -1; N[i].hpos = -1; N[i].cnt = 1;
    return i;
}
static void freenode(int64_t i) { N[i].next = nfree; nfree = i; }
static int isfrozen(int64_t i) { return fx_eq(N[i].D, INF); }
static fx T_of(int64_t r) { return fx_int(r); }          /* round r as a time */

/* ---- heap of active nodes by D */
static int lessD(int64_t a, int64_t b) { return fx_cmp(N[a].D, N[b].D) < 0; }
static void hswap(int64_t a, int64_t b) { int64_t x = H[a]; H[a] = H[b]; H[b] = x; N[H[a]].hpos = a; N[H[b]].hpos = b; }
static void hup(int64_t p) { while (p > 0) { int64_t q = (p - 1) / 2; if (!lessD(H[p], H[q])) break; hswap(p, q); p = q; } }
static void hdown(int64_t p) {
    for (;;) {
        int64_t l = 2 * p + 1, r = l + 1, s = p;
        if (l < hn && lessD(H[l], H[s])) s = l;
        if (r < hn && lessD(H[r], H[s])) s = r;
        if (s == p) break;
        hswap(p, s); p = s;
    }
}
static void hpush(int64_t i) { if (hn == hcap) { hcap = hcap ? 2 * hcap : 1 << 16; H = realloc(H, hcap * sizeof(int64_t)); } H[hn] = i; N[i].hpos = hn++; hup(hn - 1); }
static void hdel(int64_t i) { int64_t p = N[i].hpos; if (p < 0) return; hn--; if (p != hn) { hswap(p, hn); N[i].hpos = -1; hup(p); hdown(N[H[p]].hpos == p ? p : p); } N[i].hpos = -1; }
static void hfix(int64_t i) { int64_t p = N[i].hpos; if (p < 0) return; hup(p); hdown(N[i].hpos); }

/* ---- list */
static void unlink_node(int64_t i) {
    int64_t p = N[i].prev, n = N[i].next;
    if (p >= 0) N[p].next = n; else head = n;
    if (n >= 0) N[n].prev = p; else tail = p;
    hdel(i); freenode(i);
}
static void push_front(int64_t i) { N[i].prev = -1; N[i].next = head; if (head >= 0) N[head].prev = i; else tail = i; head = i; }
static void coalesce(int64_t i) {      /* i frozen: merge with frozen neighbours */
    int64_t n = N[i].next;
    if (n >= 0 && isfrozen(n)) { N[i].cnt += N[n].cnt; N[i].charged |= N[n].charged; unlink_node(n); }
    int64_t p = N[i].prev;
    if (p >= 0 && isfrozen(p)) { N[p].cnt += N[i].cnt; N[p].charged |= N[i].charged; unlink_node(i); }
}
static void freeze(int64_t i) { hdel(i); N[i].D = INF; N[i].haschain = 0; }   /* runs are coalesced in compact() */
static void compact(void) {
    int64_t i = head;
    while (i >= 0) { int64_t n = N[i].next; if (isfrozen(i) && n >= 0 && isfrozen(n)) { N[i].cnt += N[n].cnt; N[i].charged |= N[n].charged; unlink_node(n); continue; } i = n; }
}
static void check_freeze(int64_t i, fx now) { if (!isfrozen(i) && fx_cmp(fx_sub(N[i].D, now), FREEZE) > 0) freeze(i); }
static fx scale9(fx D, fx T) { return fx_add(T, fx_mul9(fx_sub(D, T))); }   /* T + 9 (D - T) */

/* ---- chain: exact size c = (c0+8/7) 8^k - 8/7 at depth q; its lifetime */
static __float128 chain_log2(int64_t c0, int64_t k, int64_t q) {
    __float128 a = (__float128)c0 + 8.0Q / 7.0Q - (8.0Q / 7.0Q) * exp2q(-3.0Q * (__float128)k);
    return log2q(a) + 3.0Q * (__float128)k - (__float128)q * LOG3;
}
#define TINYLOG (-(FRAC + 2))
static int chain_tiny(int64_t c0, int64_t k, int64_t q) { return chain_log2(c0, k, q) < TINYLOG; }

/* ---- global events */
static int64_t ng, gi; static int64_t *g_tau; static fx *g_t;
static int64_t horizon;
static int64_t *dumps, ndumps, di;
static int64_t stat_rounds1, stat_skips, stat_deaths, stat_walk, stat_maxj, stat_glob, stat_chainbig;
static int halted = 0;
static int64_t stat_glob_round;

static void print_fx(fx a) { printf("%llu %llu %llu %llu", (unsigned long long)a.w[3], (unsigned long long)a.w[2], (unsigned long long)a.w[1], (unsigned long long)a.w[0]); }
static void dump(const char *tag) {
    printf("DUMP %s tau %lld m_total %lld\n", tag, (long long)tau, (long long)m_total);
    int64_t i = head;
    while (i >= 0) {
        if (isfrozen(i)) printf("F %lld %d\n", (long long)N[i].cnt, N[i].charged);
        else {
            printf("A "); print_fx(fx_sub(N[i].D, T_of(tau)));
            printf(" %d %d %lld %lld\n", N[i].charged, N[i].haschain, (long long)N[i].c0, (long long)N[i].k);
        }
        i = N[i].next;
    }
    printf("END\n");
    fflush(stdout);
}

static int64_t ntiny_round, nbig_round, chain_dead_c0, chain_dead_k, chain_dead_j, big_dead_j;
static fx Fblk;       /* front block value at time Tlast */
static fx Tlast;
static void advanceF(fx T) { Fblk = fx_add(Fblk, fx_sub(T, Tlast)); Tlast = T; }

static void times9_prefix(int64_t stop, fx T) {   /* every active node before `stop`, and the front block */
    int64_t i = head;
    while (i >= 0 && i != stop) {
        int64_t nx = N[i].next;
        if (!isfrozen(i)) { N[i].D = scale9(N[i].D, T); N[i].haschain = 0; hfix(i); check_freeze(i, T); }
        i = nx;
    }
    Fblk = fx_mul9(Fblk);
}

static void death(int64_t x, fx T) {
    advanceF(T);
    int64_t j = 0, i = head;
    while (i != x) { i = N[i].next; j++; }
    stat_walk += j; if (j > stat_maxj) stat_maxj = j;
    int64_t r = N[x].next, l = N[x].prev;
    if (r < 0) die("death of the last node");
    if (N[x].charged) { halted = 1; printf("HALT-MODEL a charged block runs out at tau %lld index %lld\n", (long long)tau, (long long)j); }
    if (N[x].haschain) { ntiny_round++; chain_dead_c0 = N[x].c0; chain_dead_k = N[x].k; chain_dead_j = j; }
    else { nbig_round++; big_dead_j = j; }
    stat_deaths++;
    if (j == 0) die("first group runs out (only in an A phase)");
    int ch = N[r].charged;
    int rfroz = isfrozen(r), lfroz = isfrozen(l);
    if (rfroz || lfroz) {
        if (rfroz) { N[r].cnt -= 1; if (N[r].cnt == 0) unlink_node(r); }
        else unlink_node(r);
        if (!lfroz) { hdel(l); N[l].D = INF; N[l].cnt = 1; N[l].haschain = 0; }
        N[l].charged |= ch;
        unlink_node(x);
        m_total -= 2;
        times9_prefix(l, T);
        coalesce(l);
    } else {
        fx nd = fx_add(scale9(N[l].D, T), fx_sub(N[r].D, T));
        unlink_node(r); unlink_node(x);          /* change l's key only after the heap is valid again */
        N[l].D = nd; hfix(l);
        N[l].haschain = 0;
        N[l].charged |= ch;
        m_total -= 2;
        times9_prefix(l, T);
        check_freeze(l, T);
    }
}

static void global_event(fx T) {
    advanceF(T);
    stat_glob++;
    nbig_round++;
    if (tail < 0 || !isfrozen(tail) || N[tail].cnt < 3) die("global event without a right part");
    N[tail].cnt -= 2; m_total -= 2;
    times9_prefix(-1, T);
}

static void set_chain_D(void) {       /* the chain node at index 1 gets its D from the exact chain */
    if (head < 0) return;
    int64_t a = N[head].next;
    if (a < 0 || !N[a].haschain || isfrozen(a)) return;
    __float128 L = chain_log2(N[a].c0, N[a].k, m_total - 2);
    fx e;
    if (L < TINYLOG) memset(&e, 0, sizeof e);
    else if (L > 50) { N[a].haschain = 0; return; }
    else { e = fx_from_q(exp2q(L)); stat_chainbig++; }
    N[a].D = fx_add(T_of(tau), e); hfix(a);
}

static void one_round(void) {
    fx T0 = T_of(tau), T1 = T_of(tau + 1);
    memset(&Fblk, 0, sizeof Fblk); Tlast = T0; ntiny_round = nbig_round = 0; stat_glob_round = stat_glob;
    set_chain_D();
    for (;;) {
        fx Td = hn ? N[H[0]].D : INF;
        fx Tg = (gi < ng && g_tau[gi] == tau) ? fx_add(T0, g_t[gi]) : INF;
        if (fx_cmp(Td, T1) >= 0 && fx_cmp(Tg, T1) >= 0) break;
        if (fx_cmp(Tg, Td) <= 0) { global_event(Tg); gi++; continue; }
        if (fx_cmp(Td, Tlast) < 0) Td = Tlast;
        death(H[0], Td);
        if (halted) return;
    }
    advanceF(T1);
    int64_t nb = newnode();
    m_total += 1;
    N[nb].D = fx_add(T1, Fblk);
    if (nbig_round == 1 && ntiny_round == 0 && stat_glob_round == stat_glob) {
        /* exact seed of a single death at index j: newborn = 3^d + 8 3^(j-1) s + 7 3^(j-1) + 1, d its depth */
        __float128 L = log2q(7.0Q * exp2q((__float128)(big_dead_j - 1) * LOG3) + 1.0Q) - (__float128)(m_total - 1) * LOG3;
        if (L > -(__float128)FRAC) N[nb].D = fx_add(N[nb].D, fx_from_q(exp2q(L)));
    }
    if (nbig_round == 0 && ntiny_round == 0) { N[nb].haschain = 1; N[nb].c0 = 1; N[nb].k = 0; }
    else if (nbig_round == 0 && ntiny_round == 1 && chain_dead_j == 1) { N[nb].haschain = 1; N[nb].c0 = chain_dead_c0; N[nb].k = chain_dead_k + 1; }
    else if (nbig_round == 0) die("tiny death away from index 1");
    push_front(nb); hpush(nb);
    check_freeze(nb, T1);
    { int64_t a = N[nb].next; if (a >= 0) { int64_t b = N[a].next; if (b >= 0) N[b].haschain = 0; } }
    tau += 1;
    stat_rounds1++;
}

/* skip K two-round cycles when the front is [1, chain, X, rest] */
static int64_t try_skip(void) {
    int64_t a = head; if (a < 0) return 0;
    int64_t b = N[a].next; if (b < 0) return 0;
    int64_t x = N[b].next; if (x < 0) return 0;
    fx T0 = T_of(tau);
    if (!fx_eq(N[a].D, T_of(tau + 1)) || !N[b].haschain || isfrozen(b)) return 0;
    int64_t q = m_total - 2;
    if (!chain_tiny(N[b].c0, N[b].k, q)) return 0;
    if (!fx_eq(N[b].D, T0)) { N[b].D = T0; hfix(b); }
    fx best = INF;
    for (int64_t p = 0; p < hn && p < 15; p++) { int64_t id = H[p]; if (id == a || id == b || id == x) continue; if (fx_cmp(N[id].D, best) < 0) best = N[id].D; }
    int64_t K = (int64_t)1 << 60;
    if (!fx_eq(best, INF)) { fx d = fx_shr1(fx_sub(best, T0)); K = fx_floor_int(d); }
    if (gi < ng) { int64_t Kg = (g_tau[gi] - tau) / 2; if (Kg < K) K = Kg; }
    { int64_t Kh = (horizon - tau) / 2; if (Kh < K) K = Kh; }
    if (di < ndumps) { int64_t Kd = (dumps[di] - tau) / 2; if (Kd < K) K = Kd; }
    __float128 L = chain_log2(N[b].c0, N[b].k, q);
    __float128 room = ((__float128)TINYLOG - 1 - L) / 3.0Q;
    int64_t Kc = room <= 0 ? 0 : (room > 1e18Q ? (int64_t)1 << 60 : (int64_t)room);
    if (Kc < K) K = Kc;
    if (K < 1) return 0;
    tau += 2 * K;
    N[a].D = T_of(tau + 1); hfix(a);
    N[b].D = T_of(tau); hfix(b); N[b].k += K;
    if (!isfrozen(x)) { N[x].D = fx_add(N[x].D, fx_int(9 * K)); hfix(x); check_freeze(x, T_of(tau)); }
    stat_skips++;
    return K;
}

static fx read_fx(void) {
    unsigned long long w[4]; fx r;
    if (scanf("%llu %llu %llu %llu", &w[3], &w[2], &w[1], &w[0]) != 4) die("input");
    for (int i = 0; i < 4; i++) r.w[i] = w[i];
    return r;
}

int main(int argc, char **argv) {
    LOG3 = log2q(3.0Q);
    memset(&INFV, 0, sizeof INFV); INFV.w[3] = (uint64_t)1 << 62;
    ONEV = fx_int(1);
    memset(&FREEZEV, 0, sizeof FREEZEV); FREEZEV.w[2] = (uint64_t)1 << 59;
    long long t0, hor, n, extra; int64_t i;
    if (scanf("%lld %lld %lld", &t0, &hor, &extra) != 3) die("input");
    tau = t0; horizon = hor; m_total = 0;
    if (scanf("%lld", &n) != 1) die("input");
    int64_t last = -1;
    for (i = 0; i < n; i++) {
        char kind[4]; if (scanf("%3s", kind) != 1) die("input");
        int64_t id = newnode();
        if (kind[0] == 'F') { long long c; int ch; if (scanf("%lld %d", &c, &ch) != 2) die("input"); N[id].D = INF; N[id].cnt = c; N[id].charged = ch; }
        else {
            int ch, hc; long long c0, k; fx l = read_fx();
            if (scanf("%d %d %lld %lld", &ch, &hc, &c0, &k) != 4) die("input");
            N[id].D = fx_add(T_of(tau), l); N[id].charged = ch; N[id].haschain = hc; N[id].c0 = c0; N[id].k = k;
        }
        m_total += N[id].cnt;
        N[id].prev = last; if (last >= 0) N[last].next = id; else head = id; last = id;
        if (!isfrozen(id)) hpush(id);
    }
    tail = last;
    if (scanf("%lld", &n) != 1) die("input");
    ng = n; g_tau = malloc((ng + 1) * sizeof(int64_t)); g_t = malloc((ng + 1) * sizeof(fx));
    for (i = 0; i < ng; i++) { long long a; if (scanf("%lld", &a) != 1) die("input"); g_tau[i] = a; g_t[i] = read_fx(); }
    if (scanf("%lld", &n) != 1) die("input");
    ndumps = n; dumps = malloc((n + 1) * sizeof(int64_t));
    for (i = 0; i < n; i++) { long long a; if (scanf("%lld", &a) != 1) die("input"); dumps[i] = a; }
    double report = argc > 1 ? atof(argv[1]) : 0;
    double nextrep = report > 0 ? (double)tau + report : 1e300;
    while (tau < horizon && !halted) {
        while (di < ndumps && dumps[di] <= tau) { if (dumps[di] == tau) dump("at"); di++; }
        if (!try_skip()) one_round();
        if ((stat_rounds1 & 0xFFFFF) == 0 && stat_rounds1) { compact(); stat_rounds1++; }
        if ((double)tau >= nextrep) {
            fprintf(stderr, "tau %lld m %lld heap %lld nodes %lld rounds1 %lld skips %lld deaths %lld walk %lld maxj %lld glob %lld chainbig %lld\n",
                    (long long)tau, (long long)m_total, (long long)hn, (long long)nused, (long long)stat_rounds1, (long long)stat_skips,
                    (long long)stat_deaths, (long long)stat_walk, (long long)stat_maxj, (long long)stat_glob, (long long)stat_chainbig);
            nextrep *= 1.25;
        }
    }
    while (di < ndumps && dumps[di] <= tau) { if (dumps[di] == tau) dump("at"); di++; }
    printf("STATS tau %lld m %lld rounds1 %lld skips %lld deaths %lld walk %lld maxj %lld glob %lld chainbig %lld halted %d\n",
           (long long)tau, (long long)m_total, (long long)stat_rounds1, (long long)stat_skips, (long long)stat_deaths,
           (long long)stat_walk, (long long)stat_maxj, (long long)stat_glob, (long long)stat_chainbig, halted);
    dump("end");
    return 0;
}
