/* samples: run 1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE from blank tape and print "STEP n" each time the tape is
 * S(n) = C> 0 (10)^n 1 (state C on a new cell at the left end).  py/orbit.py check compares them with the map.
 * usage: gcc -O2 -o samples c/samples.c && ./samples 1000000000 > s.txt && python3 py/orbit.py check s.txt
 */
#include <stdio.h>
#include <stdlib.h>
#define N (1 << 22)
static unsigned char t[N];
/* A0 1RB A1 1RE B0 1LC B1 0RA C0 1RD C1 0LB D0 1LB D1 1RC E0 1LF E1 0RD F0 --- F1 0LE */
static const int W_[6][2] = {{1, 1}, {1, 0}, {1, 0}, {1, 1}, {1, 0}, {0, 0}};
static const int D_[6][2] = {{1, 1}, {-1, 1}, {1, -1}, {-1, 1}, {-1, 1}, {0, -1}};
static const int S_[6][2] = {{1, 4}, {2, 0}, {3, 1}, {1, 2}, {5, 3}, {-1, 4}};
int main(int argc, char **argv) {
    long long max = atoll(argv[1]);
    long long h = N / 2, lo = h, hi = h;
    int s = 0;
    for (long long k = 1; k <= max; k++) {
        int x = t[h];
        int ns = S_[s][x];
        if (ns < 0) { printf("HALT %lld\n", k); return 0; }
        t[h] = W_[s][x]; h += D_[s][x]; s = ns;
        if (h > hi) hi = h;
        if (h < lo) {
            lo = h;
            if (s == 2) {
                long long i = h + 1, n = 0;
                while (i + 1 <= hi && t[i] == 1 && t[i + 1] == 0) { n++; i += 2; }
                int ok = i <= hi && t[i] == 1;
                for (long long j = i + 1; ok && j <= hi; j++) if (t[j]) ok = 0;
                if (ok) printf("%lld %lld\n", k, n);
            }
        }
    }
    printf("END %lld\n", max);
    return 0;
}
