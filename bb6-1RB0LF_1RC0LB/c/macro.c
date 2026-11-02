/* macro: the run of 1RB0LF_1RC0LB_1RD1RB_1RE1RF_1LA---_0RC1LA from blank tape, against the macro rules.
 *
 *   macro STEPS
 *
 * At every pass start (F or B on a 0 after a left move) the tape is
 *     0^inf 1^(2s1+2) 0 1^(2s2+2) 0 ... 1^(2sp+2) [head] 0^(2h+1) 1 (0 1)^m1 0^(2n1+2) 1 (0 1)^m2 ... (0 1)^mt 0^inf
 * with h = 0 in state F, stack s1..sp >= 0, segments m >= 0 and gaps n >= -1 (n = -1 is two 1s side by side; in
 * lean/Macro.lean and py/macro.py the gap is g = n + 1).  The macro rules (BB6e.mstep, proved sound in Lean) predict
 * the next pass start from the current one.  This program runs the machine,
 * steps the macro configuration at every pass start, renders it and compares it with the machine's tape, cell by
 * cell over the whole visited tape.  Trusted computation: plain C, no proof.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static const int W[6][2] = {{1, 0}, {1, 0}, {1, 1}, {1, 1}, {1, -1}, {0, 1}};
static const int MV[6][2] = {{1, -1}, {1, -1}, {1, 1}, {1, 1}, {-1, 0}, {1, -1}};
static const int NX[6][2] = {{1, 5}, {2, 1}, {3, 1}, {4, 5}, {0, -1}, {2, 0}};
enum { A, B, C, D, E, F };
#define N (1 << 22)
#define M (1 << 20)
#define INF (-1000000)
static unsigned char tape[N];
static int stk[M], sp;          /* stack, bottom first */
static int w[M], wl;            /* the word reversed: w[wl-1] = m1, w[wl-2] = n1, ... */
static int mst, mh;             /* macro state (B or F) and head gap (INF = infinite) */
static long long stuck, nbig, ndouble, nb, nbinf, oddhist[64];

static void push(int x) { if (sp >= M) { fprintf(stderr, "stack full\n"); exit(1); } stk[sp++] = x; }
static void wpush(int x) { if (wl >= M) { fprintf(stderr, "word full\n"); exit(1); } w[wl++] = x; }

/* m(q), n(q) for q >= 1; n(q) is INF past the end */
#define MQ(q) ((q) == 0 ? 0 : w[wl - 1 - 2 * ((q) - 1)])
#define NQ(q) (wl - 2 - 2 * ((q) - 1) >= 0 ? w[wl - 2 - 2 * ((q) - 1)] : INF)

/* returns 0 on success, 1 if no rule applies */
static int mstep(void) {
    if (mst == B) {
        if (mh == INF) nbinf++; else nb++;
        int j = sp ? stk[--sp] : -1;
        if (mh != INF && mh < 1) return 1;
        if (mh == INF) wl = 0; else wpush(mh - 2);
        wpush(j + 2);
        mst = F; mh = 0;
        return 0;
    }
    int i = 1;
    while (NQ(i) == 0) i++;
    int ni = NQ(i);
    if (ni == INF || ni >= 1) {
        nbig++;
        if (i >= 2) { push(0); for (int q = 1; q <= i - 2; q++) push(MQ(q)); }
        int h = MQ(i - 1) + 2;
        wl -= 2 * (i - 1);               /* drop m1 n1 ... m_{i-1} n_{i-1}; m_i is now first */
        if (ni != INF) w[wl - 2] -= 2;
        mst = B; mh = h;
        return 0;
    }
    if (ni == -1) {
        int k = MQ(i);
        ndouble++;
        if (k < 1) return 1;
        push(0); for (int q = 1; q <= i - 1; q++) push(MQ(q));
        wl -= 2 * i;                     /* drop through n_i; m_{i+1} is now first */
        if (wl <= 0) return 1;
        int mm = w[wl - 1];
        mst = B; mh = k;
        if (wl == 1) { if (mm >= 1) w[0] = mm - 1; else { wl = 0; mh = INF; wpush(0); wl = 0; } return 0; }
        if (mm < 1) return 1;
        w[wl - 1] = mm - 1;
        return 0;
    }
    return 1;
}

/* compare the macro configuration with the tape, head at p, visited [lo, hi] */
static int same(int p, int lo, int hi, int st) {
    if (st != mst) return 0;
    int x = p;
    for (int q = sp - 1; q >= 0; q--) {
        int b = 2 * stk[q] + 2;
        for (int r = 0; r < b; r++) if (tape[--x] != 1) return 0;
        if (q > 0 && tape[--x] != 0) return 0;
    }
    for (int y = lo; y < x; y++) if (tape[y]) return 0;
    x = p;
    if (mh == INF) { for (int y = p; y <= hi; y++) if (tape[y]) return 0; return 1; }
    for (int r = 0; r < 2 * mh + 2; r++) if (tape[x++] != 0) return 0;
    if (tape[x++] != 1) return 0;
    for (int q = wl - 1; q >= 0; q--) {
        int v = w[q];
        if (((wl - 1 - q) & 1) == 0) { for (int r = 0; r < v; r++) { if (tape[x++] != 0) return 0; if (tape[x++] != 1) return 0; } }
        else { for (int r = 0; r < 2 * v + 2; r++) if (tape[x++] != 0) return 0; if (tape[x++] != 1) return 0; }
    }
    for (int y = x; y <= hi + 1; y++) if (tape[y]) return 0;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: macro STEPS\n"); return 1; }
    long long max = atoll(argv[1]), starts = 0, bad = 0;
    int p = N / 2, s = A, lo = p, hi = p, last = 0, have = 0;
    for (long long k = 1; k <= max; k++) {
        int b = tape[p];
        if (s == E && b) { printf("HALT at step %lld\n", k); return 2; }
        if ((s == F || s == B) && b == 0 && last == -1) {
            starts++;
            if (!have) {             /* the first pass start: B, empty stack, head gap 4, then 0 1 */
                mst = B; mh = 1; sp = 0; wl = 0; wpush(1); have = 1;
            }
            if (!same(p, lo, hi, s)) { if (bad < 5) printf("mismatch at step %lld\n", k); bad++; }
            int odd = 0;                 /* odd values: stack, head gap, segments and gaps (n) */
            for (int q = 0; q < sp; q++) odd += stk[q] & 1;
            if (mh != INF) odd += mh & 1;
            for (int q = 0; q < wl; q++) odd += w[q] & 1;
            oddhist[odd < 63 ? odd : 63]++;
            if (mstep()) { stuck++; if (stuck < 5) printf("no rule at step %lld\n", k); }
        }
        tape[p] = W[s][b];
        last = MV[s][b];
        p += MV[s][b];
        s = NX[s][b];
        if (p < lo) lo = p;
        if (p > hi) hi = p;
        if (p < 4 || p >= N - 4) { fprintf(stderr, "tape full\n"); return 1; }
    }
    printf("steps %lld, pass starts %lld, mismatches %lld, no rule %lld, width %d, stack %d, word %d\n",
           max, starts, bad, stuck, hi - lo + 1, sp, wl);
    printf("rules: B %lld, B with blank ahead %lld, F ending at a gap of 4 or more %lld, F ending at two 1s %lld\n",
           nb, nbinf, nbig, ndouble);
    printf("odd values per pass start:");
    for (int q = 0; q < 64; q++) if (oddhist[q]) printf(" %d: %lld", q, oddhist[q]);
    printf("\n");
    return bad || stuck;
}
