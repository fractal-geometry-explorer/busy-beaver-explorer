/* twostack: the two-stack form of the macro machine (py/twostack.py), fast, with every frame followed by identity.
 *
 *   twostack STEPS [EVERY]      run STEPS steps from the run's first F configuration; print a summary line every
 *                               EVERY steps (default 10^9) and the stats at the end
 *   twostack show STEPS EVERY   print the row (as py/twostack.py show) every EVERY steps, for the tests
 *   twostack perturb T H N SEED [K]
 *                               the control experiment of py/perturb.py: N snapshots of the run spread over its
 *                               first T steps, 5 copies of each with K (default 3) even numbers changed by 2, each
 *                               copy run H steps; prints the stats of the copies (summed) and how many got stuck
 *
 * The row is a left stack L of numbers (entries -1 below its bottom) and a right stack R of frames value<gap>, the
 * cursor on top and the end frame at the bottom.  One step is
 *
 *   R1  cursor gap n >= 1 or end:  pop b, pop a, push 0, cursor gap n - 2, then the frame (a+2)<b>
 *   R2  cursor gap -1, value x:    pop a, push 0, caller value - 1, cursor becomes (a+2)<x-2>
 *                                  (caller = end with value 0: the end becomes (a+2)<end>)
 *
 * and a frame with gap 0 is pushed onto L.  R2 needs x >= 1 and caller >= 1 (or the end); otherwise the machine is
 * stuck, which is the only way the macro machine (and so the Turing machine) can halt.
 *
 * Every frame remembers the value it was created with and how often a callee's R2 has taken 1 from it ("flips").
 * A frame created with value v can take v flips before the next one gets it stuck, so the slack v - flips at each
 * flip measures how close the run comes to getting stuck.  Trusted computation: plain C, no proof.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define END (-1000000)
#define M (1 << 20)
typedef struct { long long v; int g; int cv; int fl; } frame;
static long long L[M];
static int lp;
static frame R[M];
static int rp;
static long long steps, r1, r2, endturns, endrepl, bottom;
static long long slack[8];              /* flips of non-end frames, by slack after the flip (value left), 7 = 7+ */
static long long byflips[16][4];        /* [created value, capped 15][flips after this one, capped 3] */
static long long zero_open;              /* a flip that leaves value 0 while the frame still has turns left */
static long long last_slack0 = -1;
static long long maxL, maxR, maxv;
static int verbose;
static int stuck_at, stuck_cv, stuck_fl, stuck_self, nodd;  /* where the last stuck step happened */
static long long winflips[16], winzero[16];   /* flips of non-end frames and slack-0 flips, by decade of the step */
static long long base;                       /* in perturb: the snapshot's step, so decades are of the run's own step */
static inline int decade(long long t) { t += base; int d = 0; while (t >= 10) { t /= 10; d++; } return d; }

static inline long long popL(void) {
    if (lp == 0) { bottom++; return -1; }
    return L[--lp];
}
static inline void pushL(long long x) {
    if (lp >= M) { fprintf(stderr, "L full\n"); exit(2); }
    L[lp++] = x;
    if (lp > maxL) maxL = lp;
}
static inline void pushR(long long v, int g, int cv) {
    if (rp >= M) { fprintf(stderr, "R full\n"); exit(2); }
    R[rp].v = v; R[rp].g = g; R[rp].cv = cv; R[rp].fl = 0; rp++;
    if (rp > maxR) maxR = rp;
    if (v > maxv) maxv = v;
}
static inline void settle(void) {
    while (R[rp - 1].g == 0) { pushL(R[rp - 1].v); rp--; }
}

static void init(void) {
    /* the first F configuration of the run: 0 | 1<-1> 1<end> */
    lp = 0; rp = 0;
    pushL(0);
    pushR(1, END, 1);
    pushR(1, -1, 1);
}

/* 0 ok, 1 stuck */
static int step(void) {
    frame *c = &R[rp - 1];
    steps++;
    if (c->g == END || c->g >= 1) {
        r1++;
        if (c->g == END) endturns++;
        long long b = popL(), a = popL();
        pushL(0);
        if (c->g != END) c->g -= 2;
        if (b == 0) pushL(a + 2);
        else pushR(a + 2, (int)b, (int)(a + 2));
        settle();
        return 0;
    }
    /* gap -1 */
    r2++;
    if (c->v < 1) { stuck_self = 1; stuck_at = rp - 1; stuck_cv = c->cv; stuck_fl = c->fl; return 1; }
    long long x = c->v;
    long long a = popL();
    pushL(0);
    frame *y = &R[rp - 2];
    if (y->g == END && y->v == 0) {
        endrepl++;
        rp--;
        R[rp - 1].v = a + 2; R[rp - 1].cv = (int)(a + 2); R[rp - 1].fl = 0;
        return 0;
    }
    if (y->v < 1) { stuck_self = 0; stuck_at = rp - 2; stuck_cv = y->cv; stuck_fl = y->fl; return 1; }
    y->v--;
    y->fl++;
    if (y->g != END) {
        long long s = y->v;
        slack[s > 7 ? 7 : s]++;
        winflips[decade(steps)]++;
        if (s == 0) winzero[decade(steps)]++;
        int cv = y->cv > 15 ? 15 : y->cv, f = y->fl > 3 ? 3 : y->fl;
        byflips[cv][f]++;
        if (s == 0) {
            zero_open++; last_slack0 = steps;
            if (verbose) printf("slack 0 at step %lld: frame %d of %d from the end, created %d, gap left %d\n",
                                steps, rp - 2, rp, y->cv, y->g);
        }
    }
    c->v = a + 2; c->g = (int)(x - 2); c->cv = (int)(a + 2); c->fl = 0;
    settle();
    return 0;
}

static void reset_stats(void) {
    steps = r1 = r2 = endturns = endrepl = bottom = zero_open = 0;
    last_slack0 = -1;
    memset(slack, 0, sizeof slack);
    memset(byflips, 0, sizeof byflips);
    memset(winflips, 0, sizeof winflips);
    memset(winzero, 0, sizeof winzero);
}

static unsigned long long rng = 88172645463325252ULL;
static unsigned long long rnd(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

/* change k even numbers of the row by +-2 as py/perturb.py does: a value (L entries >= 0, R frames >= 2 after the
 * change) or an even gap that stays >= 2; every parity stays the same */
static void perturb(int k) {
    for (int t = 0; t < k; t++) {
        int n = lp + rp;
        int j = (int)(rnd() % n);
        int d = (rnd() & 1) ? 2 : -2;
        int isR = j >= lp;
        frame *f = isR ? &R[rp - 1 - (j - lp)] : NULL;
        int gap = isR ? f->g : 0;
        if ((rnd() & 1) || gap == END || gap == 0) {
            long long *v = isR ? &f->v : &L[j];
            if (*v % 2 == 0 && *v + d >= (isR ? 2 : 0)) { *v += d; if (isR) f->cv += d; }
        } else if (gap % 2 == 0 && gap + d >= 2) f->g += d;
    }
}

static void show(void) {
    printf("%lld", steps);
    for (int i = 0; i < lp; i++) printf(" %lld", L[i]);
    printf(" |");
    for (int i = rp - 1; i >= 0; i--) {
        if (R[i].g == END) printf(" %lld<end>", R[i].v);
        else printf(" %lld<%d>", R[i].v, R[i].g);
    }
    printf("\n");
}

static void summary(void) {
    long long phi = 0;
    for (int i = 0; i < lp; i++) phi += L[i];
    for (int i = 0; i < rp; i++) if (R[i].g != END) phi += R[i].v + R[i].g;
    printf("steps %lld r1 %lld r2 %lld endturns %lld endrepl %lld bottom %lld |L| %d |R| %d maxL %lld maxR %lld "
           "maxv %lld end %lld phi %lld zero_open %lld last %lld\n",
           steps, r1, r2, endturns, endrepl, bottom, lp, rp, maxL, maxR, maxv, R[0].v, phi, zero_open, last_slack0);
    printf("  flips / slack-0 flips by decade of the step:");
    for (int i = 0; i < 16; i++) if (winflips[i]) printf(" 10^%d: %lld/%lld", i, winflips[i], winzero[i]);
    printf("\n");
    fflush(stdout);
}

int main(int argc, char **argv) {
    verbose = getenv("TWOSTACK_VERBOSE") != NULL;
    init();
    if (argc > 1 && !strcmp(argv[1], "show")) {
        long long T = atoll(argv[2]), E = atoll(argv[3]);
        while (steps < T) {
            if (steps % E == 0) show();
            if (step()) { printf("stuck at %lld\n", steps); return 1; }
        }
        return 0;
    }
    if (argc > 1 && !strcmp(argv[1], "perturb")) {
        long long T = atoll(argv[2]), H = atoll(argv[3]);
        int N = atoi(argv[4]), K = argc > 6 ? atoi(argv[6]) : 3;
        rng ^= (unsigned long long)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL;
        static long long sL[M]; static frame sR[M];
        long long tslack[8] = {0}, tby[16][4] = {{0}}, tsteps = 0, tr2 = 0, tzero = 0, nstuck = 0, trials = 0;
        long long next = T / N, at = 0, twf[16] = {0}, twz[16] = {0};
        for (int s = 0; s < N; s++) {
            while (steps < next) { if (step()) { printf("run stuck?!\n"); return 1; } }
            next += T / N;
            int slp = lp, srp = rp; long long sst = steps;
            memcpy(sL, L, sizeof(long long) * lp); memcpy(sR, R, sizeof(frame) * rp);
            long long keep[6] = {r1, r2, endturns, endrepl, bottom, zero_open};
            long long kslack[8], kby[16][4]; memcpy(kslack, slack, sizeof slack); memcpy(kby, byflips, sizeof byflips);
            for (int c = 0; c < 5; c++) {
                lp = slp; rp = srp;
                memcpy(L, sL, sizeof(long long) * lp); memcpy(R, sR, sizeof(frame) * rp);
                for (int i = 0; i < rp; i++) R[i].fl = 0;
                reset_stats();
                base = sst;
                perturb(K);
                int st = 0;
                while (steps < H) if (step()) { st = 1; break; }
                trials++;
                if (st) {
                    nodd = 0;
                    for (int i = 0; i < lp; i++) nodd += L[i] & 1;
                    for (int i = 0; i < rp; i++) nodd += (R[i].v & 1) + (R[i].g != END && (R[i].g & 1));
                    nstuck++;
                    printf("snapshot %lld copy %d: stuck after %lld steps (%lld R2): %s, frame %d of %d from the end, "
                           "created %d, flips %d, odd numbers %d, |L| %d\n", sst, c, steps, r2,
                           stuck_self ? "frame at gap -1 with value 0" : "caller with value 0", stuck_at, rp, stuck_cv,
                           stuck_fl, nodd, lp);
                    fflush(stdout);
                }
                tsteps += steps; tr2 += r2; tzero += zero_open;
                for (int i = 0; i < 16; i++) { twf[i] += winflips[i]; twz[i] += winzero[i]; }
                for (int i = 0; i < 8; i++) tslack[i] += slack[i];
                for (int v = 0; v < 16; v++) for (int f = 0; f < 4; f++) tby[v][f] += byflips[v][f];
            }
            base = 0;
            lp = slp; rp = srp;
            memcpy(L, sL, sizeof(long long) * lp); memcpy(R, sR, sizeof(frame) * rp);
            steps = sst; r1 = keep[0]; r2 = keep[1]; endturns = keep[2]; endrepl = keep[3]; bottom = keep[4]; zero_open = keep[5];
            memcpy(slack, kslack, sizeof slack); memcpy(byflips, kby, sizeof byflips);
            (void)at;
        }
        printf("trials %lld stuck %lld steps %lld r2 %lld zero_open %lld\n", trials, nstuck, tsteps, tr2, tzero);
        printf("slack after a flip, 0..7+:");
        for (int i = 0; i < 8; i++) printf(" %lld", tslack[i]);
        printf("\nv=2 frames: flipped once %lld, twice %lld, 3+ %lld\n", tby[2][1], tby[2][2], tby[2][3]);
        printf("by decade of the snapshot's step plus the steps since the change: flips / slack-0 flips\n");
        for (int i = 0; i < 16; i++) if (twf[i]) printf("  10^%d: %lld / %lld\n", i, twf[i], twz[i]);
        return 0;
    }
    long long T = argc > 1 ? atoll(argv[1]) : 1000000;
    long long E = argc > 2 ? atoll(argv[2]) : 1000000000LL;
    while (steps < T) {
        if (step()) { printf("STUCK at step %lld\n", steps); show(); summary(); return 1; }
        if (steps % E == 0) summary();
    }
    summary();
    printf("slack after a flip (non-end frames), 0..7+:");
    for (int i = 0; i < 8; i++) printf(" %lld", slack[i]);
    printf("\nflips by created value (rows) and flip number 1, 2, 3+:\n");
    for (int v = 0; v < 16; v++) {
        long long t = byflips[v][1] + byflips[v][2] + byflips[v][3];
        if (t) printf("  v=%d%s: %lld %lld %lld\n", v, v == 15 ? "+" : "", byflips[v][1], byflips[v][2], byflips[v][3]);
    }
    return 0;
}
