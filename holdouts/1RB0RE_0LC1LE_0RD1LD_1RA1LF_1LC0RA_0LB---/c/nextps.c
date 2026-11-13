/* One phase of 1RB0RE_0LC1LE_0RD1LD_1RA1LF_1LC0RA_0LB---, used by ../py/phases.py.
 *
 * usage: echo "D Z" | ./nextps      D a string of 0/1 cells, Z a number
 * Starts from PS(D, Z) = D 0^Z 1 0 0 E> (blank beyond) and runs to the next PS(D', Z'): the head in state E
 * reaching a new rightmost cell just after `1 0 0`, with a run of zeros longer than half the visited tape before
 * that `1`.  Prints "D' Z' steps", or "halt steps".
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* write, move (+1 right, -1 left), next state; -1 halts.  States A..F = 0..5. */
static const int W[6][2] = {{1, 0}, {0, 1}, {0, 1}, {1, 1}, {1, 0}, {0, -1}};
static const int MV[6][2] = {{1, 1}, {-1, -1}, {1, -1}, {1, -1}, {-1, 1}, {-1, 0}};
static const int NX[6][2] = {{1, 4}, {2, 4}, {3, 3}, {0, 5}, {2, 0}, {1, -1}};

int main(void) {
    static char d[1 << 20];
    long z;
    if (scanf("%s %ld", d, &z) != 2) return 1;
    long n = strlen(d), pad = 1000, len = pad + n + z + 3 + 4 * z + 100000;
    unsigned char *t = calloc(len, 1);
    for (long i = 0; i < n; i++) t[pad + i] = d[i] - '0';
    t[pad + n + z] = 1;
    long lo = pad, pos = pad + n + z + 3, hi = pos, st = 4;
    for (long i = 0;; i++) {
        int r = t[pos];
        if (NX[st][r] < 0) { printf("halt %ld\n", i); return 0; }
        t[pos] = W[st][r]; int m = MV[st][r]; st = NX[st][r]; pos += m;
        if (pos < lo) { lo = pos; if (lo < 5) return 2; }
        if (pos > hi) {
            hi = pos;
            if (hi + 10 >= len) return 3;
            if (st == 4 && t[pos - 3] == 1 && t[pos - 2] == 0 && t[pos - 1] == 0) {
                long j = pos - 4;
                while (t[j] == 0) j--;
                long zz = pos - 4 - j;
                if (2 * zz > pos - lo) {
                    long k = lo;
                    while (t[k] == 0) k++;
                    for (long q = k - 1; q <= j; q++) putchar('0' + t[q]);
                    printf(" %ld %ld\n", zz, i + 1);
                    return 0;
                }
            }
        }
    }
}
