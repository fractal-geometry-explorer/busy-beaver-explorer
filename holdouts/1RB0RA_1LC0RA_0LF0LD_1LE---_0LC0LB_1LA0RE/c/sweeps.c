/* Sweeps of 1RB0RA_1LC0RA_0LF0LD_1LE---_0LC0LB_1LA0RE: a plain simulator that counts sweeps (B on the blank cell
 * right of the tape) and, for every sweep that reaches the leftmost 1 of the tape, prints
 *   sweep_number step blocks ones_in_inner_blocks ones_in_last_block
 * and every 2^34 steps a progress line starting with #
 * where blocks/mass are read off the tape at the end of that sweep (blocks of 10s separated by single extra 0s).
 * usage: sweeps MAX_STEPS            (gcc -O2 -o sweeps sweeps.c) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1 << 24)
static unsigned char t[N];
int main(int argc, char **argv) {
    long long max = argc > 1 ? atoll(argv[1]) : 1000000000LL;
    /* A=0..F=5; table[s][r] = write, move(+1/-1), next; -1 = halt */
    int W[6][2] = {{1,0},{1,0},{0,0},{1,-1},{0,0},{1,0}};
    int D[6][2] = {{1,1},{-1,1},{-1,-1},{-1,0},{-1,-1},{-1,1}};
    int S[6][2] = {{1,0},{2,0},{5,3},{4,-1},{2,1},{0,4}};
    long long pos = N / 2, lo = pos, hi = pos, step = 0, sweep = 0;
    long long firstone = pos; int touched = 0;
    int s = 0;
    while (step < max) {
        int r = t[pos];
        if (S[s][r] < 0) { printf("HALT at step %lld (state %c reads %d), sweep %lld\n", step + 1, 'A' + s, r, sweep); return 0; }
        t[pos] = W[s][r]; int ns = S[s][r]; pos += D[s][r]; s = ns; step++;
        if ((step & 0x3ffffffffLL) == 0) { printf("# %lld steps, %lld sweeps\n", step, sweep); fflush(stdout); }
        if (pos < lo) lo = pos;
        if (pos > hi) hi = pos;
        if (pos < 2 || pos >= N - 2) { printf("tape full\n"); return 1; }
        /* leftmost 1 */
        if (pos <= firstone) touched = 1;
        if (s == 1 && pos == hi && t[pos] == 0) {   /* B on the blank cell right of the tape: a sweep ended */
            sweep++;
            long long f = lo; while (f < hi && !t[f]) f++;
            firstone = f;
            if (touched) {
                /* blocks: split at "00" */
                long long blocks = 1, mass = 0, cur = 0, lastblk = 0;
                for (long long i = f; i < hi; i++) {
                    if (t[i]) { cur++; }
                    else if (i + 1 < hi && !t[i + 1] && t[i - 1]) { blocks++; mass += cur; cur = 0; }
                }
                lastblk = cur;
                printf("%lld %lld %lld %lld %lld\n", sweep, step, blocks, mass, lastblk);
                fflush(stdout);
            }
            touched = 0;
        }
    }
    printf("END %lld steps, %lld sweeps, width %lld\n", step, sweep, hi - lo + 1);
    return 0;
}
