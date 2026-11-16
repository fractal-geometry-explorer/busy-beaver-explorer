/* The event oracle of py/macro.py (function `oracle`) in C, for speed (16 November 2026).

   Reads lines "y word maxsteps" on stdin (word: the left part read from the head outwards, '-' for empty) and
   prints, for each, what macro.oracle returns: "HALT k", "NONE", or "yy word k" (word '-' if empty).  It runs
   1RB1LD_1LC0RE_1LA0LD_0LB0LE_0RB0LF_1RE--- from  [reverse(word)] 1 0 1 0 0 E> 0 (1110)^y 111111  until the next
   tick boundary, detected exactly as in macro.py: at a change of direction after a sweep of >= 30 cells, in state
   E on a 0, with (1110)^yy 111111 0... to the right and 10100 to the left.

   gcc -O2 -o oracle c/oracle.c */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static const char *M = "1RB1LD_1LC0RE_1LA0LD_0LB0LE_0RB0LF_1RE---";
static int W[6][2], D[6][2], S[6][2], H[6][2];

static void parse(void) {
    for (int s = 0; s < 6; s++)
        for (int r = 0; r < 2; r++) {
            const char *t = M + 7 * s + 3 * r;
            if (t[0] == '-') { H[s][r] = 1; continue; }
            H[s][r] = 0; W[s][r] = t[0] - '0'; D[s][r] = t[1] == 'R' ? 1 : -1; S[s][r] = t[2] - 'A';
        }
}

static char *tape; static long N, OFF;
#define T(i) tape[(i) + OFF]

int main(void) {
    parse();
    static char line[1 << 22];
    while (fgets(line, sizeof line, stdin)) {
        long y, maxs; char *word = malloc(strlen(line) + 1);
        if (sscanf(line, "%ld %s %ld", &y, word, &maxs) != 3) { free(word); continue; }
        long L = strcmp(word, "-") == 0 ? 0 : (long)strlen(word);
        long left_len = L + 5, right_len = 1 + 4 * y + 6;
        N = 2 * (left_len + right_len) + 4 * maxs / 1000 + (1 << 16);
        if (N > (1L << 30)) N = 1L << 30;
        OFF = N / 2;
        tape = calloc(N, 1);
        /* left = reversed(word) + [1,0,1,0,0], at indices -left_len .. -1 */
        for (long i = 0; i < L; i++) T(i - left_len) = word[L - 1 - i] - '0';
        static const char tail5[5] = {1, 0, 1, 0, 0};
        for (int i = 0; i < 5; i++) T(L + i - left_len) = tail5[i];
        /* right = [0] + [1,1,1,0]*y + [1]*6 at indices 0 .. */
        T(0) = 0;
        for (long i = 0; i < y; i++) { T(1 + 4 * i) = 1; T(2 + 4 * i) = 1; T(3 + 4 * i) = 1; T(4 + 4 * i) = 0; }
        for (int i = 0; i < 6; i++) T(1 + 4 * y + i) = 1;
        long pos = 0, lo = -left_len, hi = right_len - 1, prev = 0, last = 0; int st = 4, dirn = -1;
        int done = 0;
        for (long k = 1; k <= maxs; k++) {
            int r = T(pos);
            if (H[st][r]) { printf("HALT %ld\n", k); done = 1; break; }
            T(pos) = W[st][r]; pos += D[st][r]; st = S[st][r];
            if (pos - 8 < -OFF || pos + 8 >= N - OFF) { printf("NONE\n"); done = 1; break; }   /* out of room */
            if (pos < lo) lo = pos;
            if (pos > hi) hi = pos;
            int nd = pos > prev ? 1 : -1;
            if (nd != dirn) {
                long dd = prev - last; if (dd < 0) dd = -dd;
                if (dd >= 30 && st == 4 && T(pos) == 0) {
                    long p = pos + 1, yy = 0;
                    while (p + 3 < N - OFF && T(p) == 1 && T(p + 1) == 1 && T(p + 2) == 1 && T(p + 3) == 0) { p += 4; yy++; }
                    int ok = 1;
                    for (int j = 0; j < 6; j++) if (p + j >= N - OFF || T(p + j) != 1) ok = 0;
                    if (ok) for (long q = p + 6; q <= hi; q++) if (T(q) != 0) { ok = 0; break; }
                    if (ok) { static const char m5[5] = {1, 0, 1, 0, 0}; for (int j = 0; j < 5; j++) if (T(pos - 5 + j) != m5[j]) ok = 0; }
                    if (ok) {
                        long q = pos - 6, first = lo;
                        while (first < q && T(first) == 0) first++;
                        printf("%ld ", yy);
                        if (q < first) printf("-");
                        for (long c = q; c >= first; c--) putchar('0' + T(c));
                        printf(" %ld\n", k);
                        done = 1; break;
                    }
                }
                last = prev; dirn = nd;
            }
            prev = pos;
        }
        if (!done) printf("NONE\n");
        fflush(stdout);
        free(tape); free(word);
    }
    return 0;
}
