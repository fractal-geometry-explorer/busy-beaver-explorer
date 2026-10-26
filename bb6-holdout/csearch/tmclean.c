/* For every clean tape n in [N0, N1): run the real machine from 0^inf A>1 1 (10)^n 1 1 0^inf until the next clean tape
   (reported as a jump) or a halt. Independent of the mark model. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long long ll;
static const int WR[6][2] = {{1,0},{1,0},{1,1},{1,0},{0,0},{0,1}};
static const int MV[6][2] = {{1,1},{-1,1},{-1,-1},{-1,0},{1,-1},{-1,1}};
static const int NX[6][2] = {{1,4},{2,0},{0,3},{0,-1},{5,1},{3,4}};
int main(int argc, char **argv) {
    ll N0 = atoll(argv[1]), N1 = atoll(argv[2]);
    ll L = 4 * N1 + 4000; unsigned char *tape = malloc(L);
    ll halts = 0, maxjump = 0, total = 0; long double steps_all = 0;
    for (ll n = N0; n < N1; n++) {
        memset(tape, 0, L);
        ll base = 1000; tape[base] = 1; tape[base + 1] = 1;
        for (ll i = 0; i < n; i++) { tape[base + 2 + 2 * i] = 1; tape[base + 3 + 2 * i] = 0; }
        tape[base + 2 + 2 * n] = 1; tape[base + 3 + 2 * n] = 1;
        ll h = base, lo = base, hi = base + 3 + 2 * n; int st = 0; ll steps = 0; int done = 0;
        while (!done) {
            int sym = tape[h];
            if (steps > 0 && st == 0 && sym == 1 && tape[h + 1] == 1 && !tape[h - 1] && !tape[h - 2] && !tape[h - 3]) {
                int lb = 1; for (ll i = lo; i < h; i++) if (tape[i]) { lb = 0; break; }
                if (lb) { ll i = h + 2, pairs = 0; while (tape[i] == 1 && tape[i + 1] == 0) { pairs++; i += 2; }
                    if (tape[i] == 1 && tape[i + 1] == 1) { int rb = 1; for (ll j = i + 2; j <= hi + 1; j++) if (tape[j]) { rb = 0; break; }
                        if (rb) { ll jump = pairs - n; if (jump > maxjump) maxjump = jump; total++; steps_all += steps; done = 1; break; } } }
            }
            int nx = NX[st][sym];
            if (nx < 0) { printf("n = %lld HALTS after %lld steps\n", n, steps); halts++; done = 1; break; }
            tape[h] = WR[st][sym]; h += MV[st][sym]; st = nx; steps++;
            if (h < lo) lo = h; if (h > hi) hi = h;
            if (h < 2 || h > L - 3) { printf("n = %lld: off the buffer\n", n); done = 1; break; }
        }
    }
    printf("clean tapes %lld..%lld: %lld reached the next clean tape, %lld halted; largest jump %lld; %.3Le steps in all\n", N0, N1 - 1, total, halts, maxjump, steps_all);
}
