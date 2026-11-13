/* engine MACHINE STEPS SIDE D EVERY: the width of the changing zone ("engine") at each end of the tape.
 *
 * At every EVERY-th turn on SIDE (L or R: the last extension of the visited cells on that side before one on the
 * other side) the tape is compared with the tape at the previous such turn moved by D cells (cell x now against
 * cell x + D then).  Printed: the step, the width, and how many cells from the right end (act_right) and from the left
 * end (act_left) come before the first 200 cells in a row that agree.  -1: no such stretch.
 *   gcc -O2 -o engine c/engine.c && ./engine MACHINE 3000000000 L 16 50          (1RB0RC_1LC0RB_..., D = 16)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int T[6][2][3];
int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: engine MACHINE STEPS SIDE D EVERY\n"); return 1; }
    char *m = argv[1]; long long S = atoll(argv[2]); char side = argv[3][0]; int D = atoi(argv[4]); int EV = atoi(argv[5]);
    for (int s = 0; s < 6; s++) for (int r = 0; r < 2; r++) {
        char *t = m + 7 * s + 3 * r;
        if (t[2] == '-') { T[s][r][2] = -1; continue; }
        T[s][r][0] = t[0] - '0'; T[s][r][1] = t[1] == 'R' ? 1 : -1; T[s][r][2] = t[2] - 'A';
    }
    long N = 1L << 26;
    unsigned char *tp = calloc(N, 1), *pv = calloc(N, 1), *snap = calloc(N, 1);
    long p = N / 2, lo = p, hi = p, plo = 0, phi = -1, slo = 0, shi = -1; int st = 0, lastside = 0, have = 0;
    long long lastk = 0, turns = 0;
    for (long long k = 1; k <= S; k++) {
        int *tr = T[st][tp[p]];
        if (tr[2] < 0) { printf("halted at step %lld\n", k); return 0; }
        tp[p] = tr[0]; p += tr[1]; st = tr[2];
        if (p < 1 || p > N - 2) { printf("tape limit\n"); return 1; }
        if (p < lo || p > hi) {
            int sd = p < lo ? 'L' : 'R';
            if (p < lo) lo = p; else hi = p;
            if (lastside && sd != lastside && lastside == side) {
                turns++;
                if (have && turns % EV == 0) {
                    long run = 0, x, R = -1, L = -1;
                    for (x = shi; x >= slo; x--) {
                        long y = x + D;
                        if (y >= plo && y <= phi && snap[x] == pv[y]) { if (++run >= 200) { R = shi - (x + 199); break; } } else run = 0;
                    }
                    run = 0;
                    for (x = slo; x <= shi; x++) {
                        long y = x + D;
                        if (y >= plo && y <= phi && snap[x] == pv[y]) { if (++run >= 200) { L = x - 199 - slo; break; } } else run = 0;
                    }
                    printf("%lld width %ld act_right %ld act_left %ld\n", lastk, shi - slo + 1, R, L);
                    fflush(stdout);
                }
                memcpy(pv + slo, snap + slo, shi - slo + 1); plo = slo; phi = shi; have = 1;
            }
            if (sd == side) { memcpy(snap + lo, tp + lo, hi - lo + 1); slo = lo; shi = hi; lastk = k; }
            lastside = sd;
        }
    }
    return 0;
}
