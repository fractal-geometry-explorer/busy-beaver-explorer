/* superrun: the super orbit of 1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB, accelerated by periodic tables.
 *
 *   superrun [-S MAX_SUPER_STEPS] [-E MAX_TABLE_ENTRIES] [-d] [-q SECONDS] [-c FILE EVERY] [-P p_1,...,p_m]
 *
 * The super step (py/waves.py `superstep`, proved in lean/Wave.lean) seen from the right end: number the blocks from
 * the right, level 0 = p_m, level 1 = p_{m-1}, ...  Each super step level 0 receives a wave with h = 10.  A level
 * with block p that receives a wave h computes d = p + h; if d is odd it becomes (d + 5)/2 and the level above
 * receives an add of (d - 1)/2 (p += that, the super step ends there); if d is even it becomes d/2 and the level
 * above receives a wave with h = d/2.  The top level (the leftmost block) always passes the wave on to the left end
 * (the left-end rule of `superstep`; d_1 a power of two is the halt).  So information only flows upward: the bottom
 * k levels form an autonomous system, independent of everything above them.  Being a contraction (each wave halves
 * a level), each level settles into a cycle, and then everything level k ever receives is one periodic sequence.
 *
 * The program keeps that sequence for the bottom K levels as a table (super steps elapsed, the event, the machine
 * steps spent below level K) and runs the levels from K up explicitly.  Whenever level K's block is the same at two
 * passes through the table, level K is periodic from then on (its input is periodic and its state recurred), and
 * the table for K + 1 is built from L passes of the table for K.  A pass of the table for K stands for about
 * 2^(K+13) super steps, so the run speeds up about twofold per level.
 *
 * Machine steps: a super step (from the tape [P, 5, 0] with A on the blank right of the last block to the next such
 * tape) takes 210 + sum g(d) over the levels that receive a wave, + 17 for the level that receives the add, with
 * g(d) = (d + 1) + cyc(d - 4) + 3 + (d - 4) div 2 and cyc(c) = j(2c + 7) - 2j^2, j = c div 2.  At the left end the
 * wave goes on through virtual levels with p = 0 (d -> d/2): each costs g, an odd end costs 17, d = 3 (the visit in
 * state F) costs 16.  This is the step count of four py/waves.py `step`s (tests/test_superrun.py checks it).
 *
 * Output: "left S T d1 m K ..." for each return of the wave to the left end (super step S, counted from 1, ends at
 * machine step T; d1 = N / 2^(m-1), the machine halts iff d1 is a power of two), "table K L entries period S" when a
 * level is added to the table, "status" lines, and an "end" line with the bound.  -d runs without tables (direct); -c (direct) also writes "S T p_1 ... p_m" to FILE every
 * EVERY super steps: the tape [p_1, ..., p_m, 5, 0] after S super steps, reached at machine step T.  -P starts from
 * the tape [p_1, ..., p_m, 5, 0] at machine step 0 instead of [1, 6, 5, 0] at step 136 (for the tests).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;
typedef unsigned __int128 u128;

/* ---- fixed-width unsigned big numbers for the machine step count ---- */
#define NL 10
typedef struct { u64 w[NL]; } big;

static void die(const char *m) { fprintf(stderr, "superrun: %s\n", m); fflush(stdout); exit(2); }

static void big_addw(big *a, const u64 *b, int n) {
    u64 c = 0;
    int i;
    for (i = 0; i < n; i++) {
        u128 s = (u128)a->w[i] + b[i] + c;
        a->w[i] = (u64)s;
        c = (u64)(s >> 64);
    }
    for (; c && i < NL; i++) {
        u128 s = (u128)a->w[i] + c;
        a->w[i] = (u64)s;
        c = (u64)(s >> 64);
    }
    if (c) die("step count overflow");
}
static void big_add128(big *a, u128 v) { u64 b[2] = {(u64)v, (u64)(v >> 64)}; big_addw(a, b, 2); }

static void big_str(const big *a, char *out) {
    big t = *a;
    char buf[NL * 20 + 2];
    int k = sizeof buf - 1;
    buf[k] = 0;
    for (;;) {
        u64 r = 0;
        int zero = 1;
        for (int i = NL - 1; i >= 0; i--) {
            u128 cur = ((u128)r << 64) | t.w[i];
            t.w[i] = (u64)(cur / 1000000000u);
            r = (u64)(cur % 1000000000u);
            if (t.w[i]) zero = 0;
        }
        for (int q = 0; q < 9; q++) { buf[--k] = (char)('0' + r % 10); r /= 10; }
        if (zero) break;
    }
    while (buf[k] == '0' && buf[k + 1]) k++;
    strcpy(out, buf + k);
}
static double big_log10(const big *a) {
    long double x = 0;
    for (int i = NL - 1; i >= 0; i--) x = x * 18446744073709551616.0L + a->w[i];
    return x > 0 ? (double)log10l(x) : 0;
}

static void u128_str(u128 v, char *out) {
    char s[48];
    int k = 47;
    s[k] = 0;
    if (!v) s[--k] = '0';
    while (v) { s[--k] = (char)('0' + (int)(v % 10)); v /= 10; }
    strcpy(out, s + k);
}

/* g(d) as four 64-bit words (d < 2^126) */
static void g_big(u128 d, u64 out[4]) {
    if (d < 4) die("g: d < 4");
    u128 c = d - 4, j = c >> 1;
    u64 jl = (u64)j, jh = (u64)(j >> 64);
    /* j^2 */
    u128 ll = (u128)jl * jl, lh = (u128)jl * jh, hh = (u128)jh * jh;
    u64 w0 = (u64)ll, w1, w2, w3;
    u128 mid = (ll >> 64) + (u64)lh + (u64)lh;
    w1 = (u64)mid;
    u128 hi = (mid >> 64) + (lh >> 64) + (lh >> 64) + (u64)hh;
    w2 = (u64)hi;
    w3 = (u64)((hi >> 64) + (hh >> 64));
    /* 2 j^2 */
    w3 = (w3 << 1) | (w2 >> 63); w2 = (w2 << 1) | (w1 >> 63); w1 = (w1 << 1) | (w0 >> 63); w0 <<= 1;
    big r = {{0}};
    r.w[0] = w0; r.w[1] = w1; r.w[2] = w2; r.w[3] = w3;
    /* + (c odd ? 10 : 8) j + d + 4: these are below 2^131, add as two parts */
    u128 lin = (u128)((c & 1) ? 10 : 8) * (j >> 4);  /* < 2^127 */
    big_add128(&r, lin << 4);
    big_add128(&r, (u128)((c & 1) ? 10 : 8) * (j & 15) + d + 4);
    memcpy(out, r.w, 4 * sizeof(u64));
}
static inline u128 g_small(u64 d) {       /* d < 2^62 */
    u128 c = d - 4, j = c >> 1;
    return 2 * j * j + ((c & 1) ? 10 : 8) * j + d + 4;
}

/* ---- the table ---- */
typedef struct { u64 dt, v, c[2]; } ent;  /* v's top bit: an add (else a wave); c: machine steps below level K */
#define ADDBIT (1ull << 63)

static ent *tab;
static u64 ntab, tail_dt, tail_c[2];
static int K;

/* the machine steps of one entry stay far below 2^128 (about 2^(2K+11)); the run stops if one does not */
static inline void acc2(u64 *a, u128 v) {
    u128 x = ((u128)a[1] << 64 | a[0]), s = x + v;
    if (s < x) die("table cost overflow");
    a[0] = (u64)s;
    a[1] = (u64)(s >> 64);
}
static inline void acc2w(u64 *a, const u64 *b) { acc2(a, (u128)b[1] << 64 | b[0]); }

/* the table for K + 1 from the table for K and level K's block p0, over L passes.  Returns 0 (and changes nothing)
 * unless L passes of the table bring level K back to p0: only then is level K periodic from here on. */
static int build(u64 p0, int L, u64 maxent) {
    static int told = -1;
    u64 nw = 0;
    for (u64 i = 0; i < ntab; i++) nw += !(tab[i].v & ADDBIT);
    ent *nt = nw && nw * L <= maxent ? malloc(sizeof(ent) * nw * L) : 0;
    if (!nt) {
        if (told != K) printf("cap K %d L %d would need %llu entries\n", K, L, (unsigned long long)(nw * L));
        told = K;
        return 0;
    }
    u64 p = p0, n = 0, adt = 0, ac[2] = {0, 0};
    for (int pass = 0; pass < L; pass++) {
        for (u64 i = 0; i < ntab; i++) {
            const ent *e = &tab[i];
            adt += e->dt;
            acc2w(ac, e->c);
            if (e->v & ADDBIT) { p += e->v & ~ADDBIT; acc2(ac, 17); continue; }
            u64 d = p + e->v;
            if (d >> 62) die("table value overflow");
            acc2(ac, g_small(d));
            ent *o = &nt[n++];
            o->dt = adt;
            memcpy(o->c, ac, sizeof ac);
            if (d & 1) { o->v = ((d - 1) >> 1) | ADDBIT; p = (d + 5) >> 1; }
            else { o->v = d >> 1; p = d >> 1; }
            adt = 0; ac[0] = ac[1] = 0;
        }
        adt += tail_dt;
        acc2w(ac, tail_c);
        if (adt >> 62) die("table period overflow");
    }
    if (p != p0) { free(nt); return 0; }     /* not a cycle of the pass map (the history was a false lead) */
    free(tab);
    tab = nt; ntab = n; tail_dt = adt;
    memcpy(tail_c, ac, sizeof ac);
    K++;
    return 1;
}

/* ---- the explicit levels K, K+1, ... (index 0 = level K), and the run ---- */
#define MAXL 4096
static u128 up[MAXL];
static int nup;
static u128 S;              /* super steps done */
static big T;               /* machine steps at the end of super step S */

static double t_start;
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + ts.tv_nsec * 1e-9; }

static void addg(u128 d) {
    if (d < ((u128)1 << 62)) big_add128(&T, g_small((u64)d));
    else { u64 w[4]; g_big(d, w); big_addw(&T, w, 4); }
}

static int bits128(u128 v) { int b = 0; while (v) { b++; v >>= 1; } return b; }

static void left_end(u128 d1) {
    int s = 0;
    u128 u = d1;
    while (!(u & 1)) { u >>= 1; s++; }
    char ss[48], ds[48], ts[NL * 20 + 2];
    u128_str(S, ss); u128_str(d1, ds);
    if (u == 1) { big_str(&T, ts); printf("HALT S %s d1 %s (T before the end of this super step: %s)\n", ss, ds, ts); fflush(stdout); exit(0); }
    nup--;
    if (d1 & 1) big_add128(&T, 17);
    else {
        u128 e = d1;
        for (;;) {
            e >>= 1;
            if (e == 3) { big_add128(&T, 16); break; }
            addg(e);
            if (e & 1) { big_add128(&T, 17); break; }
        }
    }
    if (nup + s + 2 >= MAXL) die("too many levels");
    for (int t = s - 1; t >= 0; t--) up[nup++] = u << t;
    up[nup++] = (u + 5) >> 1;
    up[nup++] = (u - 1) >> 1;
    /* how close N = 2^(m-1) d1 is to a power of two: the relative distance of d1 to the nearest one */
    int b = bits128(d1);
    long double x = (long double)d1, lo = ldexpl(1.0L, b - 1), hi = ldexpl(1.0L, b);
    long double rel = fminl(x - lo, hi - x) / x;
    big_str(&T, ts);
    printf("left S %s T %s d1 %s m %d K %d bits %d s %d u_bits %d log2_reldist %.2f\n", ss, ts, ds, K + nup, K, b, s,
           bits128(u), (double)log2l(rel));
    fflush(stdout);
}

static void wave(u128 h) {
    for (int k = 0;; k++) {
        u128 d = up[k] + h;
        if (d < up[k]) die("level overflow");
        addg(d);
        if (k == nup - 1) { left_end(d); return; }
        if (d & 1) { up[k] = (d + 5) >> 1; up[k + 1] += (d - 1) >> 1; big_add128(&T, 17); return; }
        up[k] = d >> 1;
        h = d >> 1;
    }
}

static void status(const char *tag) {
    char ss[48], ts[NL * 20 + 2], ps[48];
    u128_str(S, ss); big_str(&T, ts);
    printf("%s S %s T %s log10T %.3f m %d K %d entries %llu time %.1f top", tag, ss, ts, big_log10(&T), K + nup, K,
           (unsigned long long)ntab, now() - t_start);
    for (int i = nup - 1; i >= 0 && i >= nup - 4; i--) { u128_str(up[i], ps); printf(" %s", ps); }
    printf("\n");
    fflush(stdout);
}

/* direct runs only: "S T p_1 ... p_m" (the tape [p_1, ..., p_m, 5, 0] after S super steps, at machine step T) */
static void checkpoint(FILE *f) {
    char ss[48], ts[NL * 20 + 2], ps[48];
    u128_str(S, ss); big_str(&T, ts);
    fprintf(f, "%s %s", ss, ts);
    for (int i = nup - 1; i >= 0; i--) { u128_str(up[i], ps); fprintf(f, " %s", ps); }
    fprintf(f, "\n");
    fflush(f);
}

int main(int argc, char **argv) {
    long double maxS = 1e30L;
    u64 maxent = 100000000;
    int direct = 0;
    u64 ckevery = 0;
    FILE *ck = 0;
    const char *start = 0;
    double every = 60;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "-S") && i + 1 < argc) maxS = strtold(argv[++i], 0);
        else if (!strcmp(argv[i], "-E") && i + 1 < argc) maxent = strtoull(argv[++i], 0, 10);
        else if (!strcmp(argv[i], "-q") && i + 1 < argc) every = atof(argv[++i]);
        else if (!strcmp(argv[i], "-d")) direct = 1;
        else if (!strcmp(argv[i], "-P") && i + 1 < argc) start = argv[++i];
        else if (!strcmp(argv[i], "-c") && i + 2 < argc) {
            ck = fopen(argv[++i], "w");
            ckevery = strtoull(argv[++i], 0, 10);
            if (!ck || !ckevery) die("-c FILE EVERY");
            direct = 1;
        }
        else { fprintf(stderr, "usage: superrun [-S MAX_SUPER_STEPS] [-E MAX_TABLE_ENTRIES] [-d] [-q SECONDS] [-c FILE EVERY] [-P p_1,...,p_m]\n"); return 1; }
    }
    t_start = now();
    /* the tape [1, 6, 5, 0] at step 136; level 0 receives a wave of 10 every super step, at 210 steps */
    tab = malloc(sizeof(ent));
    tab[0].dt = 1; tab[0].v = 10; tab[0].c[0] = 210; tab[0].c[1] = 0;
    ntab = 1; tail_dt = 0; tail_c[0] = tail_c[1] = 0;
    if (start) {            /* another start [p_1, ..., p_m, 5, 0], at machine step 0 */
        u128 P[MAXL];
        int m = 0;
        for (const char *q = start; *q;) {
            char *e;
            unsigned long long v = strtoull(q, &e, 10);
            if (e == q || m >= MAXL) die("-P p_1,...,p_m");
            P[m++] = v;
            q = *e == ',' ? e + 1 : e;
        }
        if (m < 1) die("-P p_1,...,p_m");
        for (nup = 0; nup < m; nup++) up[nup] = P[m - 1 - nup];
    } else {
        up[0] = 6; up[1] = 1; nup = 2;
        big_add128(&T, 136);
    }
    u128 hist[256];
    u64 wraps = 0;
    unsigned polls = 0;
    double next_status = now() + every;
    for (;;) {
        for (u64 i = 0; i < ntab; i++) {
            const ent *e = &tab[i];
            S += e->dt;
            big_addw(&T, e->c, 2);
            if (e->v & ADDBIT) { up[0] += e->v & ~ADDBIT; big_add128(&T, 17); }
            else wave(e->v);
            if (ck && S % ckevery == 0) checkpoint(ck);
            if ((long double)S >= maxS) goto done;
        }
        S += tail_dt;
        big_addw(&T, tail_c, 2);
        if (++polls >= 1u << 20 || ntab > 4096) { polls = 0; if (now() > next_status) { status("status"); next_status = now() + every; } }
        if ((long double)S >= maxS) break;
        /* is level K periodic now? */
        int found = 0;
        if (!direct && nup >= 3 && up[0] < ((u128)1 << 61)) {
            for (u64 L = 1; L <= 256 && L <= wraps; L++)
                if (hist[(wraps - L) % 256] == up[0]) {
                    u128 Q0 = 0;
                    if (build((u64)up[0], (int)L, maxent)) {
                        for (u64 q = 0; q < ntab; q++) Q0 += tab[q].dt;
                        Q0 += tail_dt;
                        memmove(up, up + 1, sizeof(u128) * (nup - 1));
                        nup--;
                        char qs[48], ss[48];
                        u128_str(Q0, qs); u128_str(S, ss);
                        printf("table K %d L %llu entries %llu period %s at S %s time %.1f\n", K, (unsigned long long)L,
                               (unsigned long long)ntab, qs, ss, now() - t_start);
                        fflush(stdout);
                        found = 1;
                    }
                    break;
                }
        }
        if (found) wraps = 0;
        else { hist[wraps % 256] = up[0]; wraps++; }
    }
done:
    status("end");
    return 0;
}
