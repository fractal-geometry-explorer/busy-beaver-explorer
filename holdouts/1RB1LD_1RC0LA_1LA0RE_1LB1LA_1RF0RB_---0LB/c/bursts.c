/* bursts MACHINE STEPS SIDE: each burst of growth of the visited cells on SIDE (L or R): the step of its last new cell,
 * the width then, and how many cells it added (a burst ends when the other side grows).
 *   gcc -O2 -o bursts c/bursts.c && ./bursts MACHINE 1000000000 L */
#include <stdio.h>
#include <stdlib.h>
static int T[6][2][3];
int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: bursts MACHINE STEPS SIDE\n"); return 1; }
    char *m = argv[1]; long long S = atoll(argv[2]); char want = argv[3][0];
    for (int s = 0; s < 6; s++) for (int r = 0; r < 2; r++) {
        char *t = m + 7 * s + 3 * r;
        if (t[2] == '-') { T[s][r][2] = -1; continue; }
        T[s][r][0] = t[0] - '0'; T[s][r][1] = t[1] == 'R' ? 1 : -1; T[s][r][2] = t[2] - 'A';
    }
    long N = 1L << 26; unsigned char *tp = calloc(N, 1); long p = N / 2, lo = p, hi = p; int st = 0, last = 0;
    long burst = 0; long long bt = 0;
    for (long long k = 1; k <= S; k++) {
        int *tr = T[st][tp[p]];
        if (tr[2] < 0) { printf("halted at step %lld\n", k); return 0; }
        tp[p] = tr[0]; p += tr[1]; st = tr[2];
        if (p < 1 || p > N - 2) { printf("tape limit\n"); return 1; }
        int sd = 0;
        if (p < lo) { lo = p; sd = 'L'; } else if (p > hi) { hi = p; sd = 'R'; }
        if (sd) {
            if (sd != last) { if (last == want) printf("%lld %c width %ld added %ld\n", bt, last, hi - lo + 1, burst); burst = 0; }
            burst++; bt = k; last = sd;
        }
    }
    return 0;
}
