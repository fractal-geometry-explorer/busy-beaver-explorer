/* crun: the pass map of lean/Pass.lean with whole growth runs taken at once (residue tables), for long runs.
 *
 * At a zigzag start t(a, 0, r) away from the boundary a growth pass is t(a, 0, r) -> t'(4q + c, 0, r - q - d) with
 * a = 3q + e and (t', c, d) fixed by (t, e) (lean/Pass.lean, grow_*; Y with e = 2 goes through y(5, 2q + 2, .), whose
 * pass is again a growth pass, and the two are taken together).  So k growth passes in a row depend only on
 * a mod 3^k: with a = 3^k Q + rho the end state is t''(A1 Q + A0, 0, r - (B1 Q + B0)), the frames F1 Q + F0 and the
 * machine steps S2 Q^2 + S1 Q + S0, and all k passes are growth passes iff r >= G1 Q + G0 (the margin r - q - 7 of the
 * last pass is the smallest).  The tables are built at start-up from the single-pass formulas (pass(), the same code
 * as c/prun.c) by exact interpolation in Q, checked on a fourth point.  A run of growth passes is taken with the
 * deepest table (k <= KMAX) whose condition holds, a drain is one pass, and the rare passes near the boundary (and the
 * passes with j != 0 after them) go by the jumps of c/frun.c, exactly as in c/prun.c.
 *
 * A halt can only come from a pass near the boundary, which is never inside a table.  Every zigzag start with
 * a = 1 mod 3, j even and |d| <= 3 (d the distance to a halting row as in c/prun.c) is a drain or a near pass, so
 * the close calls printed (|d| <= CLOSE, CLOSE <= 3) are complete.
 *
 *   crun check N            N passes by tables, each table step compared with the same passes taken one by one
 *                           (pass() / jump(), as c/prun.c): state, frames and steps (exit 1 on a mismatch)
 *   crun run N EVERY [CK]   N passes from blank tape (or from checkpoint file CK if it exists); a line every EVERY
 *                           passes, close calls with |d| <= 3, and the state written to CK (if given) at each line
 *   crun bench N            N passes, timing only
 *   crun lean N             the state after exactly N passes one by one from the first zigzag start, and the frames
 *                           from it (for lean/Close.lean, orb_frames)
 * Steps are kept as hi * 2^120 + lo (exact), frames are 128-bit, sizes 64-bit (exit 2 before an overflow).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
typedef long long I;
typedef unsigned __int128 W;
typedef __int128 SW;
#include "fcases.h"
static const char TAG[] = "zywuZYWU";
enum { z, y, w, u, Z, Y, Wt, U };

/* ---- c/prun.c: jump and pass ---- */
static I jump(int *t, I v[3], W *st, int *hc) {
    I a = v[0], b = v[1], c = v[2], k;
    if ((*t == w || *t == Wt) && b >= 2 && c >= 1) { k = b / 2; v[0] = a + 4 * k; v[1] = b - 2 * k; *st = (W)6 * k; return k; }
    if ((*t == u && b >= 1) || (*t == U && a >= 1 && b >= 1)) { v[1] = 0; v[2] = c + 2 * b; *st = (W)4 * b; return b; }
    if ((*t == y || *t == Y) && a >= 3 && c >= 2) {
        k = a / 3; if (c - 1 < k) k = c - 1;
        v[0] = a - 3 * k; v[1] = b + 2 * k; v[2] = c - k;
        *st = (W)k * (W)(4 * b + 9) + (W)4 * k * (k - 1); return 2 * k;
    }
    int r = fc_step(t, v, st);
    if (r < 0) { *hc = -1 - r; return 0; }
    return 1;
}
static int zstart(int t, I v[3]) { return (t == y || t == Y) && v[0] >= 3 && v[2] >= 2; }
static const int G[2][3][2][7] = {
  { { {y, 2, 1, 8, 17, 19, 7}, {y, 5, 4, 7, 15, 19, 7} },
    { {y, 7, 4, 8, 20, 19, 7}, {y, 4, 1, 9, 22, 19, 7} },
    { {Y, 2, 1, 6, 29, 19, 7}, {Y, 5, 4, 5, 27, 19, 7} } },
  { { {y, 5, 1, 6, 17, 19, 7}, {y, 8, 4, 5, 15, 19, 7} },
    { {y, 11, 5, 14, 47, 27, 11}, {y, 8, 2, 15, 49, 27, 11} },
    { {0} , {0} } } };
static W pass(int *t, I v[3], W *st) {
    I a = v[0], j = v[1], r = v[2], q = a / 3, e = a % 3;
    int big = *t == Y;
    if (r <= q - 1) {
        v[0] = a - 3 * r + 1; v[1] = 0; v[2] = 4 * r + 2 * j + 2;
        *st = 3 + (W)2 * j + (W)9 * r + (W)4 * j * r + (W)4 * r * r;
        return (W)j + (W)4 * r - 1;
    }
    if (r >= q + 7) {
        if (big && e == 2) {
            v[0] = 5; v[1] = j + 2 * q + 2; v[2] = r - q - 1; *t = y;
            *st = 35 + (W)13 * q + (W)4 * j + (W)4 * q * q + (W)4 * q * j;
            return 2 + (W)2 * q;
        }
        const int *g = G[big][e][j & 1];
        v[0] = 4 * q + 2 * j + g[1]; v[1] = 0; v[2] = r - q - g[2]; *t = g[0];
        *st = (W)g[4] + (W)g[5] * q + (W)g[6] * j + (W)4 * q * q + (W)4 * q * j;
        return (W)3 * q + (W)((j + g[3]) / 2);
    }
    return 0;
}
/* one pass of c/prun.c from a zigzag start (fast, else jumps to the next zigzag start); 0 on a halt */
static int onepass(int *t, I v[3], W *fr, W *st) {
    W s = 0, k = pass(t, v, &s);
    if (k) { *fr = k; *st = s; return 1; }
    *fr = 0; *st = 0;
    do { W s1 = 0; int hc = -1; I kk = jump(t, v, &s1, &hc);
         if (!kk) { *fr += 1; *st += s1; return 0; }
         *fr += kk; *st += s1; } while (!zstart(*t, v));
    return 1;
}

/* ---- tables ---- */
#define KMAX 7
typedef struct { I A1, A0, B1, B0, G1, G0, F1, F0; SW S2, S1, S0; int np, t2; } Ent;
static Ent *tab[KMAX + 1][2];
static double tau[2][KMAX + 2];   /* r / a above which k growth passes usually apply (mean of G1 / 3^k) */
static unsigned long long tauf[2][KMAX + 2];   /* tau * 2^32 */
static I p3[KMAX + 2];
static unsigned long long minv[KMAX + 2];   /* floor(2^64 / 3^k), for a / 3^k by a multiply */

/* k growth "divisions" from t(3^k Q + rho, 0, R): end state, frames, steps, passes, margin of the last pass */
static int walk2(int t, int k, I rho, I Q, I R, I *aout, I *bout, I *gout, W *fr, W *st, int *np, int *tout) {
    I v[3] = {p3[k] * Q + rho, 0, R};
    *fr = 0; *st = 0; *np = 0;
    int div = 0; I margin = 0;
    while (div < k || v[1] != 0) {
        I q = v[0] / 3;
        if (v[1] == 0) div++;
        margin = v[2] - q - 7;
        if (margin < 0) return 0;
        W s = 0, f = pass(&t, v, &s); if (!f) return 0;
        *fr += f; *st += s; (*np)++;
    }
    *aout = v[0]; *bout = R - v[2]; *gout = R - margin; *tout = t;
    return 1;
}
static void build(void) {
    p3[0] = 1; for (int i = 1; i <= KMAX + 1; i++) p3[i] = 3 * p3[i - 1];
    for (int i = 1; i <= KMAX + 1; i++) minv[i] = (unsigned long long)(((W)1 << 64) / (W)p3[i]);
    const I R = (I)1 << 58, Q0 = 1000;
    for (int k = 1; k <= KMAX; k++) for (int b = 0; b < 2; b++) {
        tab[k][b] = malloc(sizeof(Ent) * p3[k]);
        double gs = 0;
        for (I rho = 0; rho < p3[k]; rho++) {
            I A[4], B[4], Gm[4]; W Fr[4], St[4]; int np[4], t2[4];
            for (int i = 0; i < 4; i++)
                if (!walk2(b ? Y : y, k, rho, Q0 + i, R, &A[i], &B[i], &Gm[i], &Fr[i], &St[i], &np[i], &t2[i])) { fprintf(stderr, "build fail\n"); exit(3); }
            Ent *E = &tab[k][b][rho];
            E->np = np[0]; E->t2 = t2[0];
            E->A1 = A[1] - A[0]; E->A0 = A[0] - E->A1 * Q0;
            E->B1 = B[1] - B[0]; E->B0 = B[0] - E->B1 * Q0;
            E->G1 = Gm[1] - Gm[0]; E->G0 = Gm[0] - E->G1 * Q0;
            E->F1 = (I)(Fr[1] - Fr[0]); E->F0 = (I)Fr[0] - E->F1 * Q0;
            SW d1 = (SW)St[1] - (SW)St[0], d2 = (SW)St[2] - (SW)St[1];
            E->S2 = (d2 - d1) / 2; E->S1 = d1 - E->S2 * (2 * Q0 + 1); E->S0 = (SW)St[0] - E->S2 * Q0 * Q0 - E->S1 * Q0;
            for (int i = 0; i < 4; i++) {
                I Q = Q0 + i;
                if (np[i] != E->np || t2[i] != E->t2 || A[i] != E->A1 * Q + E->A0 || B[i] != E->B1 * Q + E->B0 ||
                    Gm[i] != E->G1 * Q + E->G0 || (I)Fr[i] != E->F1 * Q + E->F0 ||
                    (SW)St[i] != E->S2 * Q * Q + E->S1 * Q + E->S0) { fprintf(stderr, "fit fail k %d rho %lld\n", k, rho); exit(3); }
            }
            /* spot check at a much larger Q and at the edge of the condition */
            I Qb = 123456789 + rho, Ab, Bb, Gb, Rb; W Fb, Sb; int npb, tb;
            Rb = E->G1 * Qb + E->G0;
            if (!walk2(b ? Y : y, k, rho, Qb, Rb, &Ab, &Bb, &Gb, &Fb, &Sb, &npb, &tb) || Ab != E->A1 * Qb + E->A0 ||
                Bb != E->B1 * Qb + E->B0 || (I)Fb != E->F1 * Qb + E->F0 || (SW)Sb != E->S2 * Qb * Qb + E->S1 * Qb + E->S0) {
                fprintf(stderr, "edge check fail k %d rho %lld\n", k, rho); exit(3); }
            if (walk2(b ? Y : y, k, rho, Qb, Rb - 1, &Ab, &Bb, &Gb, &Fb, &Sb, &npb, &tb)) { fprintf(stderr, "edge not sharp k %d rho %lld\n", k, rho); exit(3); }
        }
    }
}

/* ---- big numbers ---- */
static void pw(W x, char *buf) {
    char tmp[64]; int n = 0;
    if (!x) { strcpy(buf, "0"); return; }
    while (x) { tmp[n++] = '0' + (int)(x % 10); x /= 10; }
    for (int i = 0; i < n; i++) buf[i] = tmp[n - 1 - i];
    buf[n] = 0;
}
static W pr(const char *s) { W x = 0; while (*s >= '0' && *s <= '9') x = x * 10 + (W)(*s++ - '0'); return x; }
/* hi * 2^120 + lo in decimal */
static void pbig(unsigned long long hi, W lo, char *buf) {
    unsigned int L[8] = {0}; /* base 2^32, little endian, 256 bits */
    for (int i = 0; i < 4; i++) L[i] = (unsigned int)(lo >> (32 * i));
    W h = (W)hi << 24;  /* hi * 2^120 = (hi << 24) * 2^96 */
    for (int i = 0; i < 4; i++) { unsigned long long s = (unsigned long long)L[3 + i] + (unsigned long long)(unsigned int)(h >> (32 * i)); L[3 + i] = (unsigned int)s;
        unsigned long long c = s >> 32; for (int m = 4 + i; c && m < 8; m++) { s = (unsigned long long)L[m] + c; L[m] = (unsigned int)s; c = s >> 32; } }
    char tmp[100]; int n = 0;
    for (;;) {
        int nz = 0; for (int i = 0; i < 8; i++) if (L[i]) nz = 1;
        if (!nz) break;
        unsigned long long rem = 0;
        for (int i = 7; i >= 0; i--) { unsigned long long cur = (rem << 32) | L[i]; L[i] = (unsigned int)(cur / 10); rem = cur % 10; }
        tmp[n++] = '0' + (int)rem;
    }
    if (!n) tmp[n++] = '0';
    for (int i = 0; i < n; i++) buf[i] = tmp[n - 1 - i];
    buf[n] = 0;
}
static double bigd(unsigned long long hi, W lo) { return (double)hi * ldexp(1.0, 120) + (double)lo; }

/* ---- the run ---- */
typedef struct { int t; I v[3]; I passes; W frames; unsigned long long shi; W slo; I ntab, ndrain, nnear; } St;
#define SMASK (((W)1 << 120) - 1)
static inline void addsteps(St *s, W x) { s->slo += x; if (s->slo >> 120) { s->shi += (unsigned long long)(s->slo >> 120); s->slo &= SMASK; } }
static int CLOSE = 3;

static void close_check(const St *s) {
    I a = s->v[0], j = s->v[1], r = s->v[2];
    if (a % 3 != 1 || (j & 1)) return;
    I d = r - a / 3 - (s->t == Y ? 3 : 2);
    if (d >= -CLOSE && d <= CLOSE) { printf("close pass %lld %c(%lld,%lld,%lld) d %+lld\n", s->passes + 1, TAG[s->t], a, j, r, d); fflush(stdout); }
}

/* advance from a zigzag start by one table step, a drain, or one slow pass; 0 on a halt, 2 on overflow */
static int step(St *s, int verbose) {
    I a = s->v[0], j = s->v[1], r = s->v[2], q = a / 3;
    if (j == 0 && r <= q - 1) {   /* drain */
        if (verbose) close_check(s);
        s->v[0] = a - 3 * r + 1; s->v[2] = 4 * r + 2;
        s->frames += (W)(4 * r - 1); addsteps(s, 3 + (W)9 * r + (W)4 * r * r);
        s->passes++; s->ndrain++;
        return 1;
    }
    if (j == 0 && r >= q + 7) {   /* growth run */
        const unsigned long long *tb = tauf[s->t == Y];
        int k = 1;   /* the number of thresholds r / a >= tau_m passed (an estimate; checked exactly below) */
        for (int m = 2; m <= KMAX; m++) k += ((W)(unsigned long long)r << 32) >= (W)(unsigned long long)a * tb[m];
        for (; k > 0; k--) {
            I Q = (I)(((W)(unsigned long long)a * minv[k]) >> 64), rho = a - Q * p3[k];
            if (rho >= p3[k]) { Q++; rho -= p3[k]; }   /* the estimate is low by at most 1 */
            const Ent *E = &tab[k][s->t == Y][rho];
            if (r >= E->G1 * Q + E->G0) {
                s->v[0] = E->A1 * Q + E->A0; s->v[2] = r - (E->B1 * Q + E->B0); s->t = E->t2;
                s->frames += (W)(E->F1 * Q + E->F0);
                addsteps(s, (W)(E->S2 * (SW)Q * Q + E->S1 * Q + E->S0));
                s->passes += E->np; s->ntab++;
                if (s->v[0] > ((I)1 << 61) || s->v[2] > ((I)1 << 61)) return 2;
                return 1;
            }
        }
        /* no table applies (Y with e = 2 whose second pass is near the boundary): one pass below */
    }
    /* near the boundary, or j != 0: one pass as in c/prun.c */
    if (verbose) close_check(s);
    W fr, st; int ok = onepass(&s->t, s->v, &fr, &st);
    s->frames += fr; addsteps(s, st); s->nnear++;
    if (!ok) return 0;
    s->passes++;
    return 1;
}

static void start(St *s) {
    memset(s, 0, sizeof *s);
    s->t = z; s->v[0] = 0; s->v[1] = 0; s->v[2] = 2; s->slo = 2;
    while (!zstart(s->t, s->v)) { W st = 0; int hc = -1; I k = jump(&s->t, s->v, &st, &hc); s->frames += k; addsteps(s, st); }
}
static void line(const char *tag, const St *s, double secs) {
    char b1[64], b2[100], b3[64];
    pw(s->frames, b1); pbig(s->shi, s->slo, b2); pw(s->slo, b3);
    printf("%s %lld %s %s %c %lld %lld %lld steps~%.4e tab %lld drain %lld near %lld t %.0fs\n", tag, s->passes, b1, b2,
           TAG[s->t], s->v[0], s->v[1], s->v[2], bigd(s->shi, s->slo), s->ntab, s->ndrain, s->nnear, secs);
    fflush(stdout);
}
static void save(const char *f, const St *s) {
    char tmpn[512]; snprintf(tmpn, sizeof tmpn, "%s.tmp", f);
    FILE *o = fopen(tmpn, "w"); if (!o) { perror(tmpn); return; }
    char b1[64], b3[64]; pw(s->frames, b1); pw(s->slo, b3);
    fprintf(o, "%d %lld %lld %lld %lld %s %llu %s %lld %lld %lld\n", s->t, s->v[0], s->v[1], s->v[2], s->passes, b1, s->shi, b3, s->ntab, s->ndrain, s->nnear);
    fclose(o); rename(tmpn, f);
}
static int load(const char *f, St *s) {
    FILE *i = fopen(f, "r"); if (!i) return 0;
    char b1[64], b3[64]; memset(s, 0, sizeof *s);
    int n = fscanf(i, "%d %lld %lld %lld %lld %63s %llu %63s %lld %lld %lld", &s->t, &s->v[0], &s->v[1], &s->v[2], &s->passes, b1, &s->shi, b3, &s->ntab, &s->ndrain, &s->nnear);
    fclose(i);
    if (n != 11) { fprintf(stderr, "bad checkpoint %s\n", f); exit(5); }
    s->frames = pr(b1); s->slo = pr(b3);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: crun check|run|bench N [EVERY [CKPT]]\n"); return 1; }
    build();
    I N = atoll(argv[2]);
    St s; start(&s);
    struct timespec t0, t1; clock_gettime(CLOCK_MONOTONIC, &t0);
    if (!strcmp(argv[1], "lean")) {
        char b1[64]; W f0 = s.frames;
        printf("first %c(%lld,%lld,%lld) frames %s\n", TAG[s.t], s.v[0], s.v[1], s.v[2], (pw(f0, b1), b1));
        for (I i = 0; i < N; i++) {
            W fr, st; if (!onepass(&s.t, s.v, &fr, &st)) { printf("HALT\n"); return 0; }
            s.frames += fr;
        }
        pw(s.frames - f0, b1);
        printf("orb (.y 3 0 5) %lld = some (.%c %lld %lld %lld, %s)\n", N, TAG[s.t], s.v[0], s.v[1], s.v[2], b1);
        return 0;
    }
    if (!strcmp(argv[1], "check")) {
        St r = s;  /* reference: one pass at a time */
        I nsteps = 0;
        while (s.passes < N) {
            int rc = step(&s, 0); nsteps++;
            if (rc == 2) { printf("OVERFLOW\n"); return 2; }
            while (r.passes < s.passes) {
                W fr, st; int ok = onepass(&r.t, r.v, &fr, &st); r.frames += fr; addsteps(&r, st); r.passes++;
                if (!ok) { if (rc) { printf("MISMATCH reference halts at pass %lld\n", r.passes); return 1; } break; }
            }
            if (rc == 0) { printf("HALT (both) pass %lld\n", s.passes); return 0; }
            if (r.t != s.t || r.v[0] != s.v[0] || r.v[1] != s.v[1] || r.v[2] != s.v[2] || r.frames != s.frames || r.slo != s.slo || r.shi != s.shi) {
                printf("MISMATCH at pass %lld: %c(%lld,%lld,%lld) vs reference %c(%lld,%lld,%lld)\n", s.passes, TAG[s.t], s.v[0], s.v[1], s.v[2], TAG[r.t], r.v[0], r.v[1], r.v[2]);
                return 1;
            }
        }
        clock_gettime(CLOCK_MONOTONIC, &t1);
        line("CHECKED", &s, (t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec));
        printf("table steps %lld for %lld passes, no mismatch\n", nsteps, s.passes);
        return 0;
    }
    int verbose = !strcmp(argv[1], "run");
    I every = argc > 3 ? atoll(argv[3]) : 0;
    const char *ck = argc > 4 ? argv[4] : 0;
    if (ck && load(ck, &s)) line("RESUME", &s, 0);
    I nextline = every ? (s.passes / every + 1) * every : -1;
    while (s.passes < N) {
        int rc = step(&s, verbose);
        if (rc == 0) { line("HALT", &s, 0); if (ck) save(ck, &s); return 0; }
        if (rc == 2) { line("OVERFLOW", &s, 0); return 2; }
        if (every && s.passes >= nextline) {
            clock_gettime(CLOCK_MONOTONIC, &t1);
            line("at", &s, (t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec));
            if (ck) save(ck, &s);
            nextline += every;
        }
    }
    clock_gettime(CLOCK_MONOTONIC, &t1);
    line("END", &s, (t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec));
    if (ck) save(ck, &s);
    return 0;
}
