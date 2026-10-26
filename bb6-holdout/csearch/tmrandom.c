/* Random round-start configurations on small tapes (gap at 1, head on cell 3 in state E, stripes alternating, a few
   random marks W/M/B where the alternation allows): run the real machine until it reaches a clean tape, halts, or a
   step cap. For halts, report where (distance from the right end of the content) and the configuration. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long long ll;
static const int WR[6][2] = {{1,0},{1,0},{1,1},{1,0},{0,0},{0,1}};
static const int MV[6][2] = {{1,1},{-1,1},{-1,-1},{-1,0},{1,-1},{-1,1}};
static const int NX[6][2] = {{1,4},{2,0},{0,3},{0,-1},{5,1},{3,4}};
static unsigned long long s = 88172645463325252ULL;
static unsigned long long rnd(void) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; return s; }
int main(int argc, char **argv) {
    long trials = atol(argv[1]); int Wmin = atoi(argv[2]), Wmax = atoi(argv[3]); ll cap = atoll(argv[4]);
    int L = 1 << 16; unsigned char *tape = malloc(L); char desc[512];
    long halts = 0, cleans = 0, capped = 0; long nearend = 0; long hist_dist[64] = {0};
    for (long t = 0; t < trials; t++) {
        memset(tape, 0, L); int base = 2000; int Wd = Wmin + (int)(rnd() % (Wmax - Wmin));
        int nmarks = 1 + (int)(rnd() % 4); int pos[8]; char typ[8]; int k = 0;
        /* choose distinct mark start cells in [6, Wd - 6] */
        for (int i = 0; i < nmarks; i++) pos[i] = 6 + (int)(rnd() % (Wd - 12));
        for (int i = 1; i < nmarks; i++) for (int j = i; j > 0 && pos[j] < pos[j-1]; j--) { int x = pos[j]; pos[j] = pos[j-1]; pos[j-1] = x; }
        int okc = 1; for (int i = 1; i < nmarks; i++) if (pos[i] - pos[i-1] < 6) okc = 0; if (!okc) { t--; continue; }
        /* build: cell 0 = 1, gap 000 at 1..3, then alternate; at a chosen cell insert a run matching the expected symbol */
        int c = 0; int prev; tape[base] = 1; prev = 1; c = 1;
        tape[base + 1] = 0; tape[base + 2] = 0; tape[base + 3] = 0; prev = 0; c = 4;
        int mi = 0; int dpos = 0; desc[0] = 0;
        while (c < Wd) {
            int v = 1 - prev;
            if (mi < nmarks && c >= pos[mi]) {
                int ln = (rnd() % 3 == 0) ? 3 : 2; if (v == 0) ln = 2;      /* zeros: wall 00; ones: marker 11 or block 111 */
                for (int i = 0; i < ln; i++) tape[base + c + i] = v;
                dpos += sprintf(desc + dpos, " %c%d", v == 0 ? 'W' : (ln == 2 ? 'M' : 'B'), c);
                c += ln; prev = v; mi++; continue;
            }
            tape[base + c] = v; prev = v; c++;
        }
        /* the content must end with a 1 */
        if (prev != 1) { tape[base + c] = 1; c++; }
        int content_end = base + c - 1;
        ll h = base + 3, lo = base, hi = content_end; int st = 4; ll steps = 0; int outcome = 0;
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
        if (outcome == 1) {
            halts++; ll r1 = hi + 1; while (r1 > h && !tape[r1]) r1--; ll dist = r1 - h; if (dist > 63) dist = 63; hist_dist[dist]++;
            if (dist < 16) nearend++;
            if (halts <= 8 || dist != 9) printf("halt after %lld steps, %lld cells left of the last 1; start width %d marks%s\n", steps, r1 - h, Wd, desc);
        } else if (outcome == 2) cleans++; else capped++;
    }
    printf("%ld trials: %ld reached a clean tape, %ld halted (%ld within 16 cells of the right end of the content), %ld hit the cap\n", trials, cleans, halts, nearend, capped);
    printf("halts by distance from the last 1:"); for (int i = 0; i < 64; i++) if (hist_dist[i]) printf(" %d:%ld", i, hist_dist[i]); printf("\n");
}
