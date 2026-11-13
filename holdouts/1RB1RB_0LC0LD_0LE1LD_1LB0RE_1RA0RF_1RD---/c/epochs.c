/* epochs: direct simulation of 1RB1RB_0LC0LD_0LE1LD_1LB0RE_1RA0RF_1RD--- from blank tape, printing every epoch start.
 *
 *   gcc -O2 -o epochs epochs.c && ./epochs 60000000000
 *
 * With a = 10, b = 100, c = 1000, an epoch starts at a visit of the right end (the head in state D on a new cell) where
 * the tape ends in
 *        (aaacacac)^T aaa cacb (aacaacac)^3 aacaac (baccaaa)^X bab aaa caacaac 1  D>
 * (P1 X 0 of lean/Phases.lean).  For each such visit the program prints the visit number, the step count (bbchallenge
 * count: steps done so far), T, X, and checks X = 6T + 17.  A halt is reported.  Plain simulation, nothing skipped. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define SZ (1LL << 27)
static unsigned char tp[SZ];
static long long p0;

/* does the word w (string of 0/1) end at cell e (inclusive)? */
static int ends(long long e, const char *w) {
    long long n = strlen(w);
    if (e - n + 1 < 0) return 0;
    for (long long i = 0; i < n; i++) if (tp[e - n + 1 + i] != w[i] - '0') return 0;
    return 1;
}
static char buf[4096];
static const char *enc(const char *t) {
    buf[0] = 0;
    for (; *t; t++) strcat(buf, *t == 'a' ? "10" : *t == 'b' ? "100" : "1000");
    return buf;
}
int main(int argc, char **argv) {
    long long N = atoll(argv[1]);
    int W[6][2] = {{1, 1}, {0, 0}, {0, 1}, {1, 0}, {1, 0}, {1, -1}};
    int Dd[6][2] = {{1, 1}, {-1, -1}, {-1, -1}, {-1, 1}, {1, 1}, {1, 0}};
    int S[6][2] = {{1, 1}, {2, 3}, {4, 3}, {1, 4}, {0, 5}, {3, -1}};
    char tail[256], wX[64], wT[64], mid[256];
    snprintf(tail, sizeof tail, "%s%s", enc("babaaacaacaac"), "1");
    strcpy(wX, enc("baccaaa"));
    strcpy(wT, enc("aaacacac"));
    snprintf(mid, sizeof mid, "%s", enc("aaacacbaacaacacaacaacacaacaacacaacaac"));
    long long p = SZ / 2, hi = p, ev = 0; int s = 0, ep = 0;
    long long lt = strlen(tail), lx = strlen(wX), lw = strlen(wT), lm = strlen(mid);
    for (long long k = 1; k <= N; k++) {
        int b = tp[p];
        if (S[s][b] < 0) { printf("HALT at step %lld\n", k); return 0; }
        tp[p] = W[s][b]; p += Dd[s][b]; s = S[s][b];
        if (p < 1 || p >= SZ - 1) { printf("out of tape at step %lld\n", k); return 1; }
        if (p > hi) {
            hi = p;
            if (s != 3) continue;
            ev++;
            long long e = p - 1;
            if (!ends(e, tail)) continue;
            e -= lt;
            long long X = 0;
            while (ends(e, wX)) { X++; e -= lx; }
            if (X < 2 || !ends(e, mid)) continue;
            e -= lm;
            long long T = 0;
            while (ends(e, wT)) { T++; e -= lw; }
            printf("epoch %d  visit %lld  steps %lld  T %lld  X %lld  %s\n", ep++, ev, k, T, X,
                   X == 6 * T + 17 ? "X = 6T+17" : "X != 6T+17");
            fflush(stdout);
        }
    }
    printf("no halt in %lld steps\n", N);
    return 0;
}
