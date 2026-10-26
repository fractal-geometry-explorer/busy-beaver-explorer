/* Plain direct simulation of 1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE from a tape file (head cell, state), no
   pattern checks at all: reports the step at which it halts, or that it did not within maxsteps.
   Usage: tmfast tapefile head state maxsteps */
#include <stdio.h>
#include <stdlib.h>
typedef long long ll;
static const unsigned char WR[6][2] = {{1,0},{1,0},{1,1},{1,0},{0,0},{0,1}};
static const signed char MV[6][2] = {{1,1},{-1,1},{-1,-1},{-1,0},{1,-1},{-1,1}};
static const signed char NX[6][2] = {{1,4},{2,0},{0,3},{0,-1},{5,1},{3,4}};
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); fseek(f, 0, SEEK_END); long n = ftell(f); fseek(f, 0, SEEK_SET);
    char *buf = malloc(n + 1); n = fread(buf, 1, n, f); fclose(f);
    ll head0 = atoll(argv[2]); int st = argv[3][0] - 'A'; ll maxsteps = atoll(argv[4]);
    ll MARGIN = 1 << 22; ll L = n + 2 * MARGIN; unsigned char *tape = calloc(L, 1); ll len = 0;
    for (long i = 0; i < n; i++) if (buf[i] == '0' || buf[i] == '1') tape[MARGIN + len++] = buf[i] - '0';
    ll h = MARGIN + head0, steps = 0;
    while (steps < maxsteps) {
        int s = tape[h]; int nx = NX[st][s];
        if (nx < 0) { printf("HALT at step %lld (state D reads 1), head at cell %lld\n", steps, h - MARGIN); return 0; }
        tape[h] = WR[st][s]; h += MV[st][s]; st = nx; steps++;
        if (h <= 0 || h >= L - 1) { printf("ran off the buffer at step %lld\n", steps); return 1; }
    }
    printf("no halt within %lld steps\n", maxsteps); return 0;
}
