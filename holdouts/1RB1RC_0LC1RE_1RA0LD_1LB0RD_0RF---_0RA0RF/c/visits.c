/* One visit of the right end is one leftward sweep and one rightward refill, with no turn in between.

   Runs 1RB1RC_0LC1RE_1RA0LD_1LB0RD_0RF---_0RA0RF from blank tape and counts, between consecutive visits of the
   right end in state A, the two ways the rightward pass could turn back before reaching the end: C reading a 1
   right after A (A1 -> 1RC, then C1 -> 0LD) and B reading a 0 right after A inside the tape (A0 -> 1RB, then
   B0 -> 0LC).  Both counts are 0 for every visit up to 10^9 steps.

   usage: gcc -O2 -o visits visits.c && ./visits 1000000000
*/
#include <stdio.h>
#include <stdlib.h>
static const int W[6][2] = {{1, 1}, {0, 1}, {1, 0}, {1, 0}, {0, 0}, {0, 0}};
static const int Dm[6][2] = {{1, 1}, {-1, 1}, {1, -1}, {-1, 1}, {1, 0}, {1, 1}};
static const int N[6][2] = {{1, 2}, {2, 4}, {0, 3}, {1, 3}, {5, 0}, {0, 5}};
#define SZ 4000000
static unsigned char t[SZ];
int main(int argc, char **argv) {
    long long max = argc > 1 ? atoll(argv[1]) : 1000000000LL, i, visits = 0, bounces = 0;
    int p = SZ / 2, s = 0, hi = p, prev = -1;
    for (i = 0; i < max; i++) {
        int x = t[p];
        if (s == 4 && x == 1) { printf("halted at step %lld\n", i + 1); return 0; }
        if (s == 0 && p > hi) visits++;
        if (s == 2 && x == 1 && prev == 0) bounces++;
        if (s == 1 && x == 0 && prev == 0 && p <= hi) bounces++;
        if (p > hi) hi = p;
        int d = Dm[s][x], ns = N[s][x];
        t[p] = W[s][x];
        p += d; prev = s; s = ns;
        if (p <= 0 || p >= SZ - 1) { printf("tape buffer exceeded\n"); return 1; }
    }
    printf("steps %lld visits %lld turns-in-refill %lld\n", max, visits, bounces);
    return 0;
}
