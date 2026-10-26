/* Simulate any 6-state 2-symbol machine (standard text) from blank; print the tape at chosen steps. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long long ll;
int main(int argc, char **argv) {
    const char *m = argv[1]; ll maxsteps = atoll(argv[2]); ll every = atoll(argv[3]);
    int WR[6][2], MV[6][2], NX[6][2];
    for (int s = 0; s < 6; s++) for (int b = 0; b < 2; b++) {
        const char *t = m + s * 7 + b * 3;
        if (t[0] == '-') { NX[s][b] = -1; WR[s][b] = 0; MV[s][b] = 0; continue; }
        WR[s][b] = t[0] - '0'; MV[s][b] = t[1] == 'R' ? 1 : -1; NX[s][b] = t[2] - 'A';
    }
    ll L = 1 << 24; unsigned char *tape = calloc(L, 1); ll h = L / 2, lo = h, hi = h; int st = 0;
    for (ll step = 0; step < maxsteps; step++) {
        if (step % every == 0 && step) {
            ll a = lo, b = hi; while (a < b && !tape[a]) a++; while (b > a && !tape[b]) b--;
            printf("step %lld state %c width %lld head %lld: ", step, 'A' + st, b - a + 1, h - a);
            for (ll i = a; i <= b && i < a + 150; i++) putchar(i == h ? (tape[i] ? 'I' : 'O') : '0' + tape[i]); if (b - a > 150) printf("..."); printf("\n");
        }
        int sym = tape[h]; int nx = NX[st][sym];
        if (nx < 0) { printf("HALT at step %lld\n", step); return 0; }
        tape[h] = WR[st][sym]; h += MV[st][sym]; st = nx; if (h < lo) lo = h; if (h > hi) hi = h;
        if (h < 2 || h > L - 3) { printf("tape limit at step %lld\n", step); return 0; }
    }
}
