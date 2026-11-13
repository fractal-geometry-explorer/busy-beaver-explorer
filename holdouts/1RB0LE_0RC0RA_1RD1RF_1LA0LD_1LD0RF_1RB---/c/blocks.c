/* The block list of 1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB--- at every turn of the head at the right end.

   build:  gcc -O2 -o blocks holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/c/blocks.c
   usage:  ./blocks STEPS [EVERY]      prints  step  list   at every EVERY-th right-end turn

   At a right-end turn the head is in state A on the next-to-last cell, and the tape from its first 1 to the end
   reads (10)^n0 s1 (10)^n1 s2 ... sk (10)^nk 1 1 with single separator cells s_i.  The list is printed as
   n0 s1 n1 ... nk with s = '|' for a separator 1 (it makes a pair 11) and '.' for a 0 (a pair 00).  The program
   checks that form at every turn (state A, the last two cells 1 1, every stretch between pairs of equal cells of
   even length) and stops with "BAD" if it fails; it reports a halt if there is one.  Same output as py/blocks.py,
   about 500 times faster (10^10 steps in a minute). */
#include <stdio.h>
#include <stdlib.h>

#define N (1 << 24)
static unsigned char tape[N];

int main(int argc, char **argv) {
    const char *M = "1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---";
    int W[12], D[12], S[12];
    for (int s = 0; s < 6; s++)
        for (int y = 0; y < 2; y++) {
            const char *p = M + s * 7 + y * 3;
            int i = s * 2 + y;
            if (p[0] == '-') { S[i] = -1; continue; }
            W[i] = p[0] - '0'; D[i] = p[1] == 'R' ? 1 : -1; S[i] = p[2] - 'A';
        }
    if (argc < 2) { fprintf(stderr, "usage: blocks STEPS [EVERY]\n"); return 1; }
    long long T = (long long)atof(argv[1]), every = argc > 2 ? atoll(argv[2]) : 1;
    long h = N / 2, lo = h, hi = h;
    int st = 0, d = 0;
    long long t = 0, k = 0;
    while (t < T) {
        int i = st * 2 + tape[h];
        if (S[i] < 0) { printf("HALT %lld\n", t + 1); return 0; }
        long h0 = h;
        tape[h] = W[i]; h += D[i]; st = S[i]; t++;
        if (h < lo) lo = h;
        if (h > hi) hi = h;
        if (h <= 1 || h >= N - 2) { printf("tape full at step %lld\n", t); return 1; }
        if (d == 1 && D[i] == -1 && h0 == hi) {
            k++;
            if (st != 0 || h != hi - 1 || !tape[hi] || !tape[hi - 1]) { printf("BAD %lld\n", t); return 1; }
            if (k % every) { d = D[i]; continue; }
            long a = lo;
            while (!tape[a]) a++;
            printf("%lld ", t);
            long start = a;
            for (long p = a; p < hi - 1; p++)
                if (tape[p] == tape[p + 1]) {
                    long sep = tape[p] ? p : p + 1;   /* the separator cell of the pair */
                    if ((sep - start) % 2) { printf("BAD %lld\n", t); return 1; }
                    printf("%ld%c", (sep - start) / 2, tape[p] ? '|' : '.');
                    start = sep + 1;
                }
            if ((hi - 1 - start) % 2) { printf("BAD %lld\n", t); return 1; }
            printf("%ld\n", (hi - 1 - start) / 2);
        }
        d = D[i];
    }
    return 0;
}
