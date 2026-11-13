/* samples: run 1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE from blank tape and print "STEP p r" each time the tape is
 * 0 (10)^p 0 1^r E> 0 with p >= 1 (state E at the right end, empty middle block).  py/check_map.py compares them with the map.
 * usage: gcc -O2 -o samples c/samples.c && ./samples 1000000000
 */
#include <stdio.h>
#include <stdlib.h>
#define N (1 << 22)
static unsigned char t[N];
/* table: [state][symbol] = write, move (+1/-1), next; next -1 halts */
static const int W_[6][2] = {{1, 1}, {1, 0}, {0, 1}, {0, 1}, {1, 1}, {0, 0}};
static const int D_[6][2] = {{1, 1}, {-1, 1}, {1, -1}, {0, 1}, {-1, 1}, {-1, -1}};
static const int S_[6][2] = {{1, 4}, {2, 0}, {3, 1}, {-1, 2}, {5, 4}, {1, 4}};
int main(int argc, char **argv) {
    long long max = atoll(argv[1]);
    long long h = N / 2, lo = h, hi = h;
    int s = 0;
    for (long long k = 1; k <= max; k++) {
        int x = t[h];
        int ns = S_[s][x];
        if (ns < 0) { printf("HALT %lld\n", k); return 0; }
        t[h] = W_[s][x]; h += D_[s][x]; s = ns;
        if (h < lo) lo = h;
        if (h > hi) {
            hi = h;
            if (s == 4) {
                long long i = lo, p = 0, r = 0;
                while (i < h && t[i] == 0) i++;             /* blank cells on the left */
                while (i + 1 < h && t[i] == 1 && t[i + 1] == 0) { p++; i += 2; }   /* the pairs 10 */
                int ok = p > 0;      /* p = 0 (`0 0 1^r`) only occurs inside a rule, never as a sample */
                if (ok) { if (t[i] != 0) ok = 0; else i++; }               /* the separator */
                while (ok && i < h) { if (t[i] != 1) { ok = 0; break; } r++; i++; }
                if (ok) printf("%lld %lld %lld\n", k, p, r);
            }
        }
    }
    printf("END %lld\n", max);
    return 0;
}
