/* One tick of 1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB--- from a block list.

   build:  gcc -O2 -o tick holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/c/tick.c
   usage:  ./tick LIST [LIST ...]        e.g.  ./tick '113|1.130.162.404.760'
           prints, for each LIST, the list at the next right-end turn, the number of steps, and how far left of
           the first 1 the head went

   The tape is built as c/blocks.c reads it at a right-end turn: (10)^n0 s1 (10)^n1 ... sk (10)^nk 1 1, separators
   1 for '|' and 0 for '.', blank tape around it, the head in state A on the next-to-last cell.  The machine runs
   until the head turns left from the rightmost cell visited (the next right-end turn), and the list is read off
   the same way as in c/blocks.c (with the same check of the form; "BAD" if it fails, "HALT" on a halt). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

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
    for (int arg = 1; arg < argc; arg++) {
        memset(tape, 0, N);
        long pos = N / 2, first = pos;
        const char *q = argv[arg];
        while (*q) {
            long n = strtol(q, (char **)&q, 10);
            for (long j = 0; j < n; j++) { tape[pos++] = 1; tape[pos++] = 0; }
            if (*q == '|') { tape[pos++] = 1; q++; }
            else if (*q == '.') { tape[pos++] = 0; q++; }
        }
        tape[pos] = 1; tape[pos + 1] = 1;
        long h = pos, hi = pos + 1, lo = first, mn = h;
        int st = 0, d = -1;
        long long t = 0;
        int ok = 1;
        for (;;) {
            int i = st * 2 + tape[h];
            if (S[i] < 0) { printf("HALT %lld\n", t + 1); ok = 0; break; }
            long h0 = h;
            tape[h] = W[i]; h += D[i]; st = S[i]; t++;
            if (h < lo) lo = h;
            if (h > hi) hi = h;
            if (h < mn) mn = h;
            if (h <= 1 || h >= N - 2) { printf("tape full\n"); ok = 0; break; }
            if (d == 1 && D[i] == -1 && h0 == hi) break;
            d = D[i];
        }
        if (!ok) continue;
        if (st != 0 || h != hi - 1 || !tape[hi] || !tape[hi - 1]) { printf("BAD\n"); continue; }
        long a = lo;
        while (!tape[a]) a++;
        long start = a;
        int bad = 0;
        for (long p = a; p < hi - 1; p++)
            if (tape[p] == tape[p + 1]) {
                long sep = tape[p] ? p : p + 1;
                if ((sep - start) % 2) { bad = 1; break; }
                printf("%ld%c", (sep - start) / 2, tape[p] ? '|' : '.');
                start = sep + 1;
            }
        if (bad || (hi - 1 - start) % 2) { printf(" BAD\n"); continue; }
        printf("%ld %lld %ld\n", (hi - 1 - start) / 2, t, mn - first);
    }
    return 0;
}
