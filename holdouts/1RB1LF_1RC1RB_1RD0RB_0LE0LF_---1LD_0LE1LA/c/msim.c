// msim: the block machine of lean/Macro.lean (blocks of two cells, run-length coded, a whole run of equal blocks
// crossed at once when the head leaves a block on the far side in the state it entered with), in C.
// It is the same step function as `mstep` there (the window tables are computed from the machine the same way), so a
// run of it is a run of 1RB1LF_1RC1RB_1RD0RB_0LE0LF_---1LD_0LE1LA, step for step; it stops if the machine halts.
//
// usage: msim MAXSTEPS [MAXBLOCKSTEPS] [tapes]
//   MAXSTEPS       stop once this many machine steps have run (a double, e.g. 1e18; at most 1.8e19)
//   MAXBLOCKSTEPS  stop after this many block-machine steps instead (0 = no limit), to compare with Lean's `mrun`
//   tapes          also print the run lists at every merge at the left end
// Output: one line per merge at the left end of the tape (the first 1-block about to empty):
//   LEFTMERGE steps=S X0=a X1=b ratio=a/b
// where a is the leftmost block (01)^a and b the block right of the emptying 1-block, both counted in blocks of two
// cells (pairs), as they stand when the head is at the left end;  "HALT" if the machine halts; at the end
//   END blocksteps=K steps=S runs=... ones=...
// Merges inside the tape are reported as INTMIN lines when a left/right block ratio is the smallest so far.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned long long u64;
static const char *M = "1RB1LF_1RC1RB_1RD0RB_0LE0LF_---1LD_0LE1LA";
static int nw[6][2], mv[6][2], ns[6][2];
// window tables [state][block][entry side: 0 = from the left, 1 = from the right]
static int tq[6][4][2], ty[6][4][2], td[6][4][2], tn[6][4][2], th[6][4][2];
#define CAP (1 << 20)
// stacks of runs, nearest run last; index 0 is the blank bottom (never popped)
static int lb[CAP], rb[CAP];
static u64 lc[CAP], rc[CAP];
static int ln = 1, rn = 1;

static void tables(void) {
    for (int s = 0; s < 6; s++)
        for (int r = 0; r < 2; r++) {
            const char *t = M + 7 * s + 3 * r;
            if (t[2] == '-') { ns[s][r] = -1; continue; }
            nw[s][r] = t[0] - '0'; mv[s][r] = t[1] == 'R' ? 1 : -1; ns[s][r] = t[2] - 'A';
        }
    for (int q = 0; q < 6; q++)
        for (int x = 0; x < 4; x++)
            for (int d = 0; d < 2; d++) {
                int c[2] = {x >> 1, x & 1}, i = d, s = q, n = 0;
                th[q][x][d] = 0;
                while (i >= 0 && i < 2) {
                    int t = ns[s][c[i]];
                    if (t < 0) { th[q][x][d] = 1; break; }
                    int w = nw[s][c[i]], m = mv[s][c[i]];
                    c[i] = w; i += m; s = t; n++;
                }
                tq[q][x][d] = s; ty[q][x][d] = c[0] * 2 + c[1]; td[q][x][d] = i >= 2 ? 0 : 1; tn[q][x][d] = n;
            }
}

static void push(int *b, u64 *c, int *n, int x, u64 k) {
    if (*n > 1 && b[*n - 1] == x) c[*n - 1] += k;
    else {
        b[*n] = x; c[*n] = k; (*n)++;
        if (*n >= CAP) { fprintf(stderr, "too many runs\n"); exit(1); }
    }
}

static void print_runs(void) {
    for (int j = rn - 1; j > 0; j--) printf("%d%d^%llu ", rb[j] >> 1, rb[j] & 1, rc[j]);
    printf("\n");
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: msim MAXSTEPS [MAXBLOCKSTEPS] [tapes]\n"); return 1; }
    double MAX = atof(argv[1]);
    u64 maxms = argc > 2 ? strtoull(argv[2], 0, 10) : 0;
    int tapes = argc > 3;
    tables();
    lb[0] = rb[0] = 0; lc[0] = rc[0] = 1;
    int q = 0, d = 0;   // d = 0: facing the right stack
    u64 steps = 0, ms = 0, lastY = 0, nleft = 0;
    double next = 1e6, minint = 1e300;
    while ((double)steps < MAX && (maxms == 0 || ms < maxms)) {
        ms++;
        int *fb, *bb, *fn, *bn; u64 *fc, *bc;
        if (d == 0) { fb = rb; fc = rc; fn = &rn; bb = lb; bc = lc; bn = &ln; }
        else        { fb = lb; fc = lc; fn = &ln; bb = rb; bc = rc; bn = &rn; }
        if (d == 1 && ln == 1 && rn >= 4) {
            // the head is at the left end of the tape: the whole tape is on the right stack
            int i = rn - 1;
            if (rb[i - 1] == 3 && rc[i - 1] <= 2 && (rb[i - 2] == 1 || rb[i - 2] == 2) && rc[i - 2] != lastY) {
                u64 X = rc[i], Y = rc[i - 2];
                lastY = Y; nleft++;
                printf("LEFTMERGE steps=%llu X0=%llu X1=%llu ratio=%.4f\n", steps, X, Y, (double)X / Y);
                if (tapes) { printf("  TAPE "); print_runs(); }
                fflush(stdout);
            }
            for (int j = i - 1; j >= 2; j--)
                if (rb[j] == 3 && rc[j] <= 2 && (rb[j + 1] == 1 || rb[j + 1] == 2) && (rb[j - 1] == 1 || rb[j - 1] == 2)
                    && rc[j - 1] >= 15) {
                    double r = (double)rc[j + 1] / rc[j - 1];
                    if (r < minint) {
                        minint = r;
                        printf("INTMIN steps=%llu a=%llu b=%llu ratio=%.4f\n", steps, rc[j + 1], rc[j - 1], r);
                    }
                }
        }
        int x = fb[*fn - 1];
        if (*fn > 1) { if (--fc[*fn - 1] == 0) (*fn)--; }
        if (th[q][x][d]) { printf("HALT within the block-machine step after machine step %llu\n", steps); return 0; }
        int q2 = tq[q][x][d], y = ty[q][x][d], d2 = td[q][x][d], n = tn[q][x][d];
        if (q2 == q && d2 == d) {
            // the head crosses the block in its state: cross the whole run of equal blocks
            u64 c = 1;
            if (*fn > 1 && fb[*fn - 1] == x) { c += fc[*fn - 1]; (*fn)--; }
            steps += c * n;
            push(bb, bc, bn, y, c);
        } else {
            steps += n;
            if (d2 == 0) push(lb, lc, &ln, y, 1); else push(rb, rc, &rn, y, 1);
        }
        q = q2; d = d2;
        if ((double)steps >= next) {
            fprintf(stderr, "%.3e steps, %d+%d runs, %llu left-end merges\n", (double)steps, ln - 1, rn - 1, nleft);
            next *= 10;
        }
    }
    u64 ones = 0;
    for (int i = 1; i < ln; i++) ones += lc[i] * ((lb[i] >> 1) + (lb[i] & 1));
    for (int i = 1; i < rn; i++) ones += rc[i] * ((rb[i] >> 1) + (rb[i] & 1));
    printf("END blocksteps=%llu steps=%llu runs=%d+%d ones=%llu state=%c\n", ms, steps, ln - 1, rn - 1, ones, 'A' + q);
    return 0;
}
