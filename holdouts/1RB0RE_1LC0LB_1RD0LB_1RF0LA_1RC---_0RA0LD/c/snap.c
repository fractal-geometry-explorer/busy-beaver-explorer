/* snap MACHINE MAXSTEPS EVERY SIDE: run from blank tape; at every EVERY-th visit of the head to the SIDE (L or R)
 * end of the visited tape, at the first new cell of the visit, print
 *   "visit step width state cells"   (cells: the visited tape, left to right, as 0/1)
 * gcc -O2 -o snap holdouts/1RB0RE_1LC0LB_1RD0LB_1RF0LA_1RC---_0RA0LD/c/snap.c */
#include <stdio.h>
#include <stdlib.h>
int W[8][2], D[8][2], S[8][2];
int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: snap MACHINE MAXSTEPS EVERY SIDE\n"); return 1; }
    const char *m = argv[1]; long long N = atoll(argv[2]), E = atoll(argv[3]); char side = argv[4][0];
    for (int s = 0; s < 6; s++) for (int y = 0; y < 2; y++) {
        const char *t = m + 7 * s + 3 * y;
        if (t[2] == '-') { S[s][y] = -1; continue; }
        W[s][y] = t[0] - '0'; D[s][y] = t[1] == 'R' ? 1 : -1; S[s][y] = t[2] - 'A';
    }
    long long size = 1LL << 27; unsigned char *c = calloc(size, 1); long long p = size / 2, lo = p, hi = p, n = 0;
    int st = 0; char last = 0;
    for (long long k = 1; k <= N; k++) {
        int y = c[p], s2 = S[st][y];
        if (s2 < 0) { printf("HALT %lld\n", k); return 0; }
        c[p] = W[st][y]; p += D[st][y]; st = s2;
        if (p < lo || p > hi) {
            char sd = p < lo ? 'L' : 'R';
            if (p < lo) lo = p; else hi = p;
            if (p < 2 || p > size - 3) { fprintf(stderr, "tape full\n"); return 1; }
            if (sd != last) {
                last = sd;
                if (sd == side && ++n % E == 0) {
                    printf("%lld %lld %lld %c ", n, k, hi - lo + 1, 'A' + st);
                    for (long long i = lo; i <= hi; i++) putchar('0' + c[i]);
                    putchar('\n'); fflush(stdout);
                }
            }
        }
    }
    return 0;
}
