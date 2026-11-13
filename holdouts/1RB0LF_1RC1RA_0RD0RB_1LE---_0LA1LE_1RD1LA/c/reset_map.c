/* reset_map: the one-number map of 1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA.
 *
 *   gcc -O2 -o reset_map reset_map.c && ./reset_map X0 X1 [MAXSTEPS]
 *
 * For each X in X0..X1 the machine is started (bbchallenge step count) from the configuration
 *     S(X) = 0^inf 1^X 1 1 1 0 B> 0^inf      (X ones, then 1110, the head in B on the blank cell after it)
 * and run until it is again in that shape: the head in B extends the visited part of the tape to the right and the
 * tape is 0^inf 1^Y 1110 B> 0^inf.  It prints "X Y STEPS" (f(X) = Y), "X HALT STEPS" when the machine halts first,
 * or "X TIMEOUT" after MAXSTEPS steps (default 4*10^9).  The run from blank tape reaches S(13) at step 110 and then
 * passes through S(29), S(45), S(137), ... : its whole future is the orbit of 13 under f.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define W 400000
static unsigned char tape[W];
int main(int argc, char **argv) {
    const char *m = "1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA";
    int nw[6][2], mv[6][2], ns[6][2];
    for (int s = 0; s < 6; s++)
        for (int r = 0; r < 2; r++) {
            const char *p = m + s * 7 + r * 3;
            if (p[0] == '-') ns[s][r] = -1;
            else { nw[s][r] = p[0] - '0'; mv[s][r] = p[1] == 'R' ? 1 : -1; ns[s][r] = p[2] - 'A'; }
        }
    if (argc < 3) { fprintf(stderr, "usage: reset_map X0 X1 [MAXSTEPS]\n"); return 1; }
    long X0 = atol(argv[1]), X1 = atol(argv[2]);
    long long maxt = argc > 3 ? atoll(argv[3]) : 4000000000LL;
    setvbuf(stdout, NULL, _IOLBF, 0);
    for (long X = X0; X <= X1; X++) {
        if (X + 10 > W / 4) { printf("%ld TOOBIG\n", X); continue; }
        memset(tape, 0, sizeof tape);
        long long base = W / 4, lo = base, hi;
        for (long i = 0; i < X + 3; i++) tape[base + i] = 1;
        long long pos = base + X + 4; hi = pos;
        int st = 1, done = 0; long long t = 0;
        while (t < maxt) {
            int r = tape[pos];
            if (ns[st][r] < 0) { printf("%ld HALT %lld\n", X, t + 1); done = 1; break; }
            tape[pos] = nw[st][r]; pos += mv[st][r]; st = ns[st][r]; t++;
            if (pos < lo) lo = pos;
            if (pos < 2 || pos > W - 2) { printf("%ld OUT\n", X); done = 1; break; }
            if (pos > hi) {
                hi = pos;
                if (st == 1 && !tape[pos - 1] && tape[pos - 2] && tape[pos - 3] && tape[pos - 4]) {
                    long long y = pos - 5, c = 0;
                    while (tape[y]) { c++; y--; }
                    int ok = 1;
                    for (long long z = lo; z <= y; z++) if (tape[z]) { ok = 0; break; }
                    if (ok) { printf("%ld %lld %lld\n", X, c, t); done = 1; break; }
                }
            }
        }
        if (!done) printf("%ld TIMEOUT\n", X);
    }
    return 0;
}
