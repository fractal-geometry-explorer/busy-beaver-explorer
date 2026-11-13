/* prehalt MACHINE STEPS: how often the run from blank tape enters the state of the halting transition, by the
 * (state, symbol) it comes from.  A halt needs one of these entries to land on the halting symbol.
 *   gcc -O2 -o prehalt c/prehalt.c && ./prehalt MACHINE 1000000000 */
#include <stdio.h>
#include <stdlib.h>
static int T[6][2][3];
int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: prehalt MACHINE STEPS\n"); return 1; }
    char *m = argv[1]; long long S = atoll(argv[2]); int hs = -1, hb = -1;
    for (int s = 0; s < 6; s++) for (int r = 0; r < 2; r++) {
        char *t = m + 7 * s + 3 * r;
        if (t[2] == '-') { T[s][r][2] = -1; hs = s; hb = r; continue; }
        T[s][r][0] = t[0] - '0'; T[s][r][1] = t[1] == 'R' ? 1 : -1; T[s][r][2] = t[2] - 'A';
    }
    long N = 1L << 24; unsigned char *tp = calloc(N, 1); long p = N / 2; int st = 0; long long cnt[6][2] = {{0}};
    for (long long k = 1; k <= S; k++) {
        int *tr = T[st][tp[p]];
        if (tr[2] < 0) { printf("halted at step %lld\n", k); return 0; }
        if (tr[2] == hs) cnt[st][tp[p]]++;
        tp[p] = tr[0]; p += tr[1]; st = tr[2];
        if (p <= 0 || p >= N - 1) { printf("tape limit at step %lld\n", k); return 1; }
    }
    printf("halting transition %c%d; entries into %c in %lld steps:", 'A' + hs, hb, 'A' + hs, S);
    for (int s = 0; s < 6; s++) for (int r = 0; r < 2; r++) if (cnt[s][r]) printf(" %c%d %lld", 'A' + s, r, cnt[s][r]);
    printf("\n");
    return 0;
}
