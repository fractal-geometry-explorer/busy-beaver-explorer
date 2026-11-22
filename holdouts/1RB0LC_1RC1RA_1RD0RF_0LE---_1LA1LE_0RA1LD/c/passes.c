/* passes.c: the passes of 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD between visits to the left end.
 *
 * usage: passes FROM TO [ENDS]
 *   Runs TO steps from blank tape. At each visit of the head to the leftmost visited cell in state C at step >= FROM,
 *   prints: step, steps since the previous such visit, "turn" T (how far right of the left end the head got in
 *   between), "len" L (width of the visited tape), and the 81 cells around the turning point with '|' after it.
 *   With a third argument, prints only the visits where the head reached the right end in between (T == L) and the
 *   stretch took more than 10^6 steps (no cells).
 * build: gcc -O2 -o passes passes.c
 */
#include <stdio.h>
#include <stdlib.h>
int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: passes FROM TO [ENDS]\n"); return 1; }
    long long from = atoll(argv[1]), to = atoll(argv[2]); int ends = argc > 3;
    const char *m = "1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD"; int W[6][2], D[6][2], N[6][2];
    for (int s = 0; s < 6; s++) for (int b = 0; b < 2; b++) {
        const char *x = m + 7 * s + 3 * b;
        if (x[0] == '-') { N[s][b] = -1; continue; }
        W[s][b] = x[0] - '0'; D[s][b] = x[1] == 'R' ? 1 : -1; N[s][b] = x[2] - 'A';
    }
    long long S = 1LL << 26; unsigned char *t = calloc(S, 1);
    long long p = S / 2, lo = p, hi = p, mx = p, last = 0; int st = 0;
    for (long long k = 1; k <= to; k++) {
        int b = t[p], ns = N[st][b];
        if (ns < 0) { printf("HALT %lld\n", k); return 0; }
        t[p] = W[st][b]; p += D[st][b]; st = ns;
        if (p <= 0 || p >= S - 1) { fprintf(stderr, "tape full at step %lld\n", k); return 2; }
        if (p < lo) lo = p; if (p > hi) hi = p; if (p > mx) mx = p;
        if (st == 2 && p == lo) {
            if (k >= from && (!ends || (mx == hi && k - last > 1000000))) {
                printf("%lld %lld turn %lld len %lld", k, k - last, mx - lo, hi - lo);
                if (!ends) { putchar(' '); for (long long i = mx - 40; i <= mx + 40; i++) { if (i == mx + 1) putchar('|'); putchar(i < lo || i > hi ? '.' : '0' + t[i]); } }
                putchar('\n'); fflush(stdout);
            }
            last = k; mx = p;
        }
    }
    printf("running %lld\n", to); return 0;
}
