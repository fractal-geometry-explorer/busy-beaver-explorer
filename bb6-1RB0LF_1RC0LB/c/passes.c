/* passes: the run of 1RB0LF_1RC0LB_1RD1RB_1RE1RF_1LA---_0RC1LA from blank tape, checked at every pass start.
 *
 *   passes STEPS [EVERY]
 *
 * A pass starts when the head turns right: F or B, having just moved left, reads a 0 and moves right (lean/Pass.lean,
 * start_F, start_B); C then enters a gap.  (B also reads 0s inside a pass, crossing gaps of 1; those are not starts.)
 * At each pass start this program
 *   - predicts how the pass ends from the cells ahead (lean/Pass.lean, pass_outcome): it crosses gaps of 1 and 2 and
 *     stops at the first other gap, which halts if its length is 3; it tallies the length of that stopping gap
 *     (0 = two 1s side by side, "blank" = the gap runs into the blank end of the tape);
 *   - checks the parity invariant: every run of 0s or of 1s of length >= 3 that has cells of the other symbol on both
 *     sides, and is not next to the head, has even length.
 * It also runs the machine itself (a halt would be reported).  Prints a progress line every EVERY steps (default
 * none), then the totals.  Trusted computation: plain C, no proof.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* A0 1RB A1 0LF B0 1RC B1 0LB C0 1RD C1 1RB D0 1RE D1 1RF E0 1LA E1 halt F0 0RC F1 1LA */
static const int W[6][2] = {{1, 0}, {1, 0}, {1, 1}, {1, 1}, {1, -1}, {0, 1}};
static const int MV[6][2] = {{1, -1}, {1, -1}, {1, 1}, {1, 1}, {-1, 0}, {1, -1}};
static const int NX[6][2] = {{1, 5}, {2, 1}, {3, 1}, {4, 5}, {0, -1}, {2, 0}};
enum { A, B, C, D, E, F };
#define N (1 << 22)
static unsigned char tape[N];
static long long ending[66]; /* gap length that ends a pass: 0..63, 64 = longer, 65 = blank end */
static long long oddruns, starts;

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: passes STEPS [EVERY]\n"); return 1; }
    long long max = atoll(argv[1]), every = argc > 2 ? atoll(argv[2]) : 0;
    int p = N / 2, s = A, lo = p, hi = p, last = 0; /* last: the previous move */
    for (long long k = 1; k <= max; k++) {
        int b = tape[p];
        if (s == E && b) { printf("HALT at step %lld\n", k); return 2; }
        if ((s == F || s == B) && b == 0 && last == -1) {
            starts++;
            /* C will stand on p+1, entering a gap whose first cell is p.  Walk the gaps. */
            int x = p + 1, g;
            for (;;) {
                g = 1;                         /* the gap's first cell (p, or the cell after the last 1) */
                while (x <= hi && !tape[x]) { g++; x++; }
                if (x > hi) { g = 65; break; } /* ran into the blank end */
                if (g != 1 && g != 2) break;
                x++;                           /* the 1 that ends the gap */
                if (x <= hi && tape[x]) { g = 0; break; } /* two 1s side by side */
                x++;                           /* the next gap's first cell */
            }
            ending[g > 64 && g != 65 ? 64 : g]++;
            /* the parity invariant */
            int y = lo;
            while (y <= hi && !tape[y]) y++;
            while (y <= hi) {
                int c = tape[y], st = y, l = 0;
                while (y <= hi && tape[y] == c) { l++; y++; }
                if (y > hi) break;             /* the last run touches the blank end */
                if (l >= 3 && (l & 1) && !(p >= st - 1 && p <= y)) {
                    if (oddruns < 10) printf("odd run: step %lld, %d^%d at %d, head %d\n", k, c, l, st - N / 2, p - N / 2);
                    oddruns++;
                }
            }
        }
        tape[p] = W[s][b];
        int ns = NX[s][b];
        last = MV[s][b];
        p += MV[s][b];
        s = ns;
        if (p < lo) lo = p;
        if (p > hi) hi = p;
        if (p < 4 || p >= N - 4) { fprintf(stderr, "tape full\n"); return 1; }
        if (every && k % every == 0) {
            printf("progress %lld steps, %lld pass starts, %lld odd runs, width %d\n", k, starts, oddruns, hi - lo + 1);
            fflush(stdout);
        }
    }
    printf("steps %lld, pass starts %lld, odd runs %lld, width %d\n", max, starts, oddruns, hi - lo + 1);
    printf("passes ending at gap 3 (would halt): %lld\n", ending[3]);
    for (int i = 0; i < 66; i++)
        if (ending[i]) {
            if (i == 65) printf("  blank end: %lld\n", ending[i]);
            else if (i == 64) printf("  gap > 63: %lld\n", ending[i]);
            else printf("  gap %d: %lld\n", i, ending[i]);
        }
    return 0;
}
