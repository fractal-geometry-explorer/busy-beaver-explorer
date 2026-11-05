/* fastrun: the run from blank tape in the two-stack form (py/twostack.py), as fast as plain C allows: no frame
 * identities (c/twostack.c follows those), entries -1 preset below L, saved states for runs in pieces.
 *
 *   fastrun run STEPS [STATE_IN|- [STATE_OUT]]   run from blank (or from a saved state) to STEPS steps
 *   fastrun dump STEPS                           print the row after each of the first STEPS steps (for tests)
 *   fastrun perturb S H K SEED                   run to S steps, then K times: change one even entry by +-2 (as
 *                                                 py/perturb.py does) and run H steps; one line per trial
 *
 * The row is the left stack L (plain numbers, entries -1 below its bottom) and the right stack R of frames v<n>, the
 * end entry at the bottom of R (gap END), the cursor at the top of R.  Frames with gap 0 belong to L, so after every
 * step they are moved there.  One step:
 *
 *   R1  gap n >= 1 or END:  a, b, x<n>      ->  0, (a+2)<b>, x<n-2>     (b the top of L, a the entry below it)
 *   R2  gap n = -1:         a, x<-1>, y<m>  ->  0, (a+2)<x-2>, (y-1)<m>  needs x >= 1 and y >= 1
 *                           a, x<-1>, 0<END> -> 0, (a+2)<END>
 *
 * Started from 0 | 1<-1> 1<end> (py/callstack.start()), it agrees with twostack.zstep step by step
 * (tests/test_accel.py).  `run` prints a line at every power of 10 and every 10^11 steps (saving the state there if
 * STATE_OUT is given), the row at the end, and one line (and the row) for every near miss: a step that takes a frame other than the end entry down to
 * value 0.  Such a frame survives only if it returns before anything else happens to it: one more R2 under it, or an
 * odd gap of its own reaching -1, needs value >= 1.  If no rule applies the machine is stuck (it halts); that is
 * printed with the row and the program exits with status 3.  Trusted computation: plain C, no proof.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define END INT32_MIN
#define PAD (1 << 20)          /* entries -1 below the bottom of L */
#define CAP (1 << 22)
typedef struct { int32_t v, n; } fr;

static int32_t Lbuf[PAD + CAP], *L = Lbuf + PAD;  /* L[lowl..nl-1], bottom first; below lowl every entry is -1 */
static int64_t nl, lowl;                          /* lowl: lowest nl reached (may be negative) */
static fr R[CAP];
static int64_t nr;
static int64_t steps, nr2, nto1, nzero, nendzero, nendrep, maxl, maxr;
static int quiet;

static void init(void) {
    for (int i = 0; i < PAD; i++) Lbuf[i] = -1;
    nl = 0; nr = 0; steps = nr2 = nto1 = nzero = nendzero = nendrep = maxl = maxr = lowl = 0;
    L[nl++] = 0;
    R[nr].v = 1; R[nr].n = END; nr++;
    R[nr].v = 1; R[nr].n = -1; nr++;
}

static void dump(FILE *o) {
    fprintf(o, "  L (bottom first):");
    for (int64_t i = lowl; i < nl; i++) fprintf(o, " %d", L[i]);
    fprintf(o, "\n  R (cursor first):");
    for (int64_t i = nr - 1; i >= 0; i--) {
        if (R[i].n == END) fprintf(o, " %d<end>", R[i].v); else fprintf(o, " %d<%d>", R[i].v, R[i].n);
    }
    fprintf(o, "\n");
}

/* One step.  Returns 0, or 1 (stuck: own value 0 at R2), or 2 (stuck: caller value 0 at R2). */
static inline int step(void) {
    fr *c = &R[nr - 1];
    int32_t n = c->n;
    if (n != -1) {
        int32_t b = L[--nl], a = L[--nl];
        if (nl < lowl) lowl = nl;
        L[nl++] = 0;
        if (n != END) c->n = n - 2;
        if (b == 0) L[nl++] = a + 2;
        else { R[nr].v = a + 2; R[nr].n = b; nr++; }
    } else {
        int32_t x = c->v;
        if (x < 1) return 1;
        int32_t a = L[--nl];
        if (nl < lowl) lowl = nl;
        fr *y = c - 1;
        if (y->n == END && y->v == 0) {
            L[nl++] = 0;
            y->v = a + 2;
            nr--;
            nendrep++;
        } else {
            if (y->v < 1) { nl++; return 2; }
            L[nl++] = 0;
            y->v--;
            if (y->n == END) { if (y->v == 0) nendzero++; }
            else if (y->v == 1) nto1++;
            else if (y->v == 0) {
                nzero++;
                if (!quiet) {
                    printf("near miss: step %lld, a frame taken to 0 with gap %d, %lld frames above the end\n",
                           (long long)steps + 1, y->n, (long long)(nr - 2));
                    dump(stdout);
                    fflush(stdout);
                }
            }
            c->v = a + 2;
            c->n = x - 2;
        }
        nr2++;
    }
    while (R[nr - 1].n == 0) { L[nl++] = R[nr - 1].v; nr--; }
    steps++;
    return 0;
}

static void save(const char *f) {
    FILE *o = fopen(f, "wb");
    if (!o) { perror(f); exit(2); }
    int64_t h[11] = {steps, nr2, nto1, nzero, nendzero, nendrep, maxl, maxr, nl, nr, lowl};
    fwrite(h, sizeof h, 1, o);
    fwrite(L + lowl, sizeof *L, nl - lowl, o);
    fwrite(R, sizeof *R, nr, o);
    fclose(o);
}

static void load(const char *f) {
    FILE *i = fopen(f, "rb");
    if (!i) { perror(f); exit(2); }
    int64_t h[11];
    if (fread(h, sizeof h, 1, i) != 1) exit(2);
    steps = h[0]; nr2 = h[1]; nto1 = h[2]; nzero = h[3]; nendzero = h[4]; nendrep = h[5]; maxl = h[6]; maxr = h[7];
    nl = h[8]; nr = h[9]; lowl = h[10];
    if (fread(L + lowl, sizeof *L, nl - lowl, i) != (size_t)(nl - lowl) || fread(R, sizeof *R, nr, i) != (size_t)nr)
        exit(2);
    fclose(i);
}

static void line(const char *tag, double t0) {
    printf("%s steps %lld R2 %lld to1 %lld zero %lld end0 %lld endrep %lld |L| %lld |R| %lld max|R| %lld "
           "end %d %.0fs\n", tag, (long long)steps, (long long)nr2, (long long)nto1, (long long)nzero,
           (long long)nendzero, (long long)nendrep, (long long)(nl - lowl), (long long)nr, (long long)maxr, R[0].v, (double)(time(0) - t0));
    fflush(stdout);
}

/* run until steps == T or stuck; returns the step() result */
static int run_to(int64_t T, int64_t *next10, int64_t *next11, const char *out, double t0) {
    while (steps < T) {
        int64_t stop = T;
        if (next10 && *next10 < stop) stop = *next10;
        if (next11 && *next11 < stop) stop = *next11;
        if (stop > ((steps >> 20) + 1) << 20) stop = ((steps >> 20) + 1) << 20;   /* chunks at multiples of 2^20 */
        while (steps < stop) {
            int r = step();
            if (r) return r;
        }
        if (nl > maxl) maxl = nl;
        if (nr > maxr) maxr = nr;
        if (nl > CAP - 1000 || nr > CAP - 1000 || -lowl > PAD - 1000) { fprintf(stderr, "stacks full\n"); exit(2); }
        if (next10 && steps == *next10) { line("10^k", t0); *next10 *= 10; }
        if (next11 && steps == *next11) { line("chk", t0); *next11 += 100000000000LL; if (out) save(out); }
    }
    return 0;
}

static uint64_t rng = 88172645463325252ULL;
static uint64_t rnd(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: see the comment at the top of fastrun.c\n"); return 1; }
    init();
    double t0 = time(0);
    if (!strcmp(argv[1], "dump")) {
        quiet = 1;
        int64_t T = atoll(argv[2]);
        for (int64_t t = 0; t < T; t++) {
            int r = step();
            printf("step %lld\n", (long long)steps + (r != 0));
            if (r) { printf("STUCK %d\n", r); break; }
            dump(stdout);
        }
        return 0;
    }
    if (!strcmp(argv[1], "run")) {
        int64_t T = (int64_t)strtod(argv[2], 0);
        if (argc > 3 && strcmp(argv[3], "-")) load(argv[3]);
        int64_t next10 = 10, next11 = 100000000000LL;
        while (next10 <= steps) next10 *= 10;
        while (next11 <= steps) next11 += 100000000000LL;
        int r = run_to(T, &next10, &next11, argc > 4 ? argv[4] : 0, t0);
        if (r) {
            printf("STUCK at step %lld: %s\n", (long long)steps + 1, r == 1 ? "own value 0 at R2" : "caller value 0 at R2");
            line("stuck", t0);
            dump(stdout);
            return 3;
        }
        line("final", t0);
        dump(stdout);
        if (argc > 4) save(argv[4]);
        return 0;
    }
    if (!strcmp(argv[1], "perturb")) {
        quiet = 1;
        int64_t S = (int64_t)strtod(argv[2], 0), H = (int64_t)strtod(argv[3], 0);
        int K = atoi(argv[4]);
        rng ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL;
        if (run_to(S, 0, 0, 0, t0)) { printf("the run itself got stuck\n"); return 3; }
        static int32_t L0[PAD + CAP]; static fr R0[CAP];
        int64_t nl0 = nl, nr0 = nr, low0 = lowl, s0 = steps;
        memcpy(L0, Lbuf, sizeof Lbuf); memcpy(R0, R, nr * sizeof *R);
        for (int k = 0; k < K; k++) {
            memcpy(Lbuf + PAD + low0, L0 + PAD + low0, (nl0 - low0) * sizeof *L); memcpy(R, R0, nr0 * sizeof *R);
            nl = nl0; nr = nr0; lowl = low0; steps = s0; nr2 = nto1 = nzero = 0;
            /* one change: an even value of L (>= 0 after), an even value of an R frame other than the end (>= 2
               after), or an even gap of an R frame (>= 2 after) */
            int64_t tot = nl + 2 * (nr - 1), j;
            int d = (rnd() & 1) ? 2 : -2;
            char what[64];
            for (;;) {
                j = rnd() % tot;
                if (j < nl) {
                    if (L[j] % 2 == 0 && L[j] + d >= 0) { L[j] += d; snprintf(what, sizeof what, "L[%lld]", (long long)j); break; }
                } else {
                    int64_t q = 1 + (j - nl) / 2;
                    if ((j - nl) % 2 == 0) {
                        if (R[q].v % 2 == 0 && R[q].v + d >= 2) { R[q].v += d; snprintf(what, sizeof what, "R[%lld].v", (long long)q); break; }
                    } else if (R[q].n % 2 == 0 && R[q].n + d >= 2) { R[q].n += d; snprintf(what, sizeof what, "R[%lld].n", (long long)q); break; }
                }
                d = (rnd() & 1) ? 2 : -2;
            }
            int r = run_to(s0 + H, 0, 0, 0, t0);
            printf("trial %d change %s %+d: %s after %lld steps, R2 %lld, to1 %lld, zero %lld\n", k, what, d,
                   r ? "STUCK" : "running", (long long)(steps - s0 + (r != 0)), (long long)nr2, (long long)nto1,
                   (long long)nzero);
            fflush(stdout);
        }
        return 0;
    }
    fprintf(stderr, "unknown mode %s\n", argv[1]);
    return 1;
}
