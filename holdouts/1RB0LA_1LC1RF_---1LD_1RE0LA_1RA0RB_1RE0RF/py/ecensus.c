// How close 1RB0LA_1LC1RF_---1LD_1RE0LA_1RA0RB_1RE0RF comes to halting: the machine halts exactly when E reads a 1
// whose right neighbour is 0 (E1 -> 0RB, B0 -> 1LC, C0 halts).  Counts, over the first N steps, the times E reads a
// 1, by the number k of 1s in a row from the head cell (E>1^k 0), and where the smallest k happened.
// build: gcc -O2 -o ecensus ecensus.c     usage: ./ecensus N
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define W (1 << 22)
static unsigned char tape[W];
int main(int argc, char **argv) {
    long long N = atoll(argv[1]);
    // A0 1RB  A1 0LA  B0 1LC  B1 1RF  C0 --- C1 1LD  D0 1RE  D1 0LA  E0 1RA  E1 0RB  F0 1RE  F1 0RF
    int wr[6][2] = {{1,0},{1,1},{0,1},{1,0},{1,0},{1,0}};
    int mv[6][2] = {{1,-1},{-1,1},{0,-1},{1,-1},{1,1},{1,1}};
    int nx[6][2] = {{1,0},{2,5},{-1,3},{4,0},{0,1},{4,5}};
    long long pos = W / 2, hi = pos, cnt[64] = {0}, at[64] = {0};
    int s = 0;
    for (long long n = 0; n < N; n++) {
        int x = tape[pos];
        if (s == 4 && x == 1) {
            int k = 0;
            while (k < 63 && tape[pos + k]) k++;
            if (!cnt[k]) at[k] = n;
            cnt[k]++;
        }
        if (s == 2 && x == 0) { printf("HALT at step %lld\n", n + 1); return 0; }
        tape[pos] = wr[s][x]; pos += mv[s][x]; s = nx[s][x];
        if (pos <= 0 || pos >= W - 64) { printf("tape out of range\n"); return 1; }
        if (pos > hi) hi = pos;
    }
    printf("E reading 1 in %lld steps, by k (E>1^k then 0):\n", N);
    for (int k = 0; k < 64; k++) if (cnt[k]) printf("  k=%d: %lld times, first at step %lld\n", k, cnt[k], at[k]);
    return 0;
}
