/* Random loop-like states G 1, W a, W b, W c on tapes of width E (a odd, b even, c odd, E even), real machine:
   fraction that halts, by tape width. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
typedef long long ll;
static const int WR[6][2] = {{1,0},{1,0},{1,1},{1,0},{0,0},{0,1}};
static const int MV[6][2] = {{1,1},{-1,1},{-1,-1},{-1,0},{1,-1},{-1,1}};
static const int NX[6][2] = {{1,4},{2,0},{0,3},{0,-1},{5,1},{3,4}};
static unsigned long long s = 0x9E3779B97F4A7C15ULL;
static unsigned long long rnd(void) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; return s; }
static double U(void) { return (rnd() >> 11) / 9007199254740992.0; }
int main(int argc, char **argv) {
    int Ewant = atoi(argv[1]); long trials = atol(argv[2]);
    int L = 8 * Ewant + 10000; unsigned char *tape = malloc(L);
    long halts = 0, cleans = 0, other = 0, near = 0;
    for (long t = 0; t < trials; t++) {
        int E = (Ewant + (int)(rnd() % (Ewant / 8 + 1))) & ~1;
        int a = ((int)(E * (0.05 + 0.3 * U()))) | 1, b = ((int)(E * (0.4 + 0.5 * U()))) & ~1;
        double f = U(); int c = (E - 2 - (int)(E * 0.3 * f * f)) | 1; if (c >= E - 1) c -= 2;
        if (!(5 < a && a + 4 < b && b + 4 < c && c < E - 2)) { t--; continue; }
        memset(tape, 0, L); int base = 1000;
        /* alternating with walls */
        int prev = 1; tape[base] = 1; tape[base + 1] = tape[base + 2] = tape[base + 3] = 0; prev = 0;
        int mk[3] = {a, b, c}, mi = 0, ok = 1;
        for (int i = 4; i < E; i++) {
            int v;
            if (mi < 3 && i == mk[mi] + 1) { v = prev; mi++; }
            else v = 1 - prev;
            if (mi < 3 && i == mk[mi] && v != 0) { ok = 0; break; }
            tape[base + i] = v; prev = v;
        }
        if (!ok || prev != 1) { t--; continue; }
        ll h = base + 3, lo = base, hi = base + E - 1; int st = 4; ll steps = 0, cap = (ll)E * E * 400; int outcome = 0;
        while (steps < cap) {
            int sym = tape[h];
            if (steps > 0 && st == 0 && sym == 1 && tape[h + 1] == 1 && !tape[h - 1] && !tape[h - 2]) {
                int lb = 1; for (ll i = lo; i < h; i++) if (tape[i]) { lb = 0; break; }
                if (lb) { ll i = h + 2; while (tape[i] == 1 && tape[i + 1] == 0) i += 2;
                    if (tape[i] == 1 && tape[i + 1] == 1) { int rb = 1; for (ll j = i + 2; j <= hi + 1; j++) if (tape[j]) { rb = 0; break; } if (rb) { outcome = 2; break; } } }
            }
            int nx = NX[st][sym];
            if (nx < 0) { outcome = 1; break; }
            tape[h] = WR[st][sym]; h += MV[st][sym]; st = nx; steps++;
            if (h < lo) lo = h; if (h > hi) hi = h;
            if (h < 5 || h > L - 5) { outcome = 3; break; }
        }
        if (outcome == 1) { halts++; ll r1 = hi + 1; while (r1 > h && !tape[r1]) r1--; if (r1 - h == 9) near++; }
        else if (outcome == 2) cleans++; else other++;
    }
    printf("E ~ %d: %ld trials, %ld halts (%ld at the right-end signature), %ld clean, %ld other; halt fraction %.3g\n", Ewant, trials, halts, near, cleans, other, (double)halts / trials);
}
