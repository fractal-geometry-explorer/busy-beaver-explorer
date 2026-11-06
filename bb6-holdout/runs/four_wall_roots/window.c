/* window: every clean tape n whose width 2n + 6 lies within 2*HALF below a target's width, run in the mark model
   (fast.h with 128-bit positions) through its whole cycle (to the next clean tape), every three-wall round start
   G 1, W a, W b, W c compared with the targets (b, W, R = W - c - 1; a free).  Untrusted.
   usage: window targets.txt HALF [MAXR] [SHARD NSHARD]     (targets.txt: lines "route i tag b W R", from targets.py) */
#include <stdio.h>
#include <stdlib.h>
#include "fast128.h"   /* make: sed "s/^typedef int64_t ll;/typedef __int128 ll;/" ../../blankrun/fast.h > fast128.h */
typedef struct { ll b, W, R; char tag[48]; } Tg;
static Tg tg[4096]; static int ntg;
static ll rd(const char *s) { ll x = 0; while (*s >= '0' && *s <= '9') x = x * 10 + (*s++ - '0'); return x; }
static void pr(ll x) { char s[50]; int i = 49; s[i] = 0; if (x == 0) s[--i] = '0'; int neg = x < 0; if (neg) x = -x;
    while (x > 0) { s[--i] = '0' + (int)(x % 10); x /= 10; } if (neg) s[--i] = '-'; fputs(s + i, stdout); }
static int cmpW(const void *x, const void *y) { ll a = ((const Tg *)x)->W, b = ((const Tg *)y)->W; return a < b ? -1 : a > b; }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); ll HALF = atoll(argv[2]); int MAXR = argc > 3 ? atoi(argv[3]) : 100000;
    char r1[16], r2[32], t[16], sb[64], sw[64], sr[64];
    while (fscanf(f, "%15s %31s %15s %63s %63s %63s", r1, r2, t, sb, sw, sr) == 6) {
        Tg *g = &tg[ntg++]; g->b = rd(sb); g->W = rd(sw); g->R = rd(sr); snprintf(g->tag, 48, "%s:%s:%s", r1, r2, t);
    }
    qsort(tg, ntg, sizeof(Tg), cmpW);
    long long cycles = 0, rounds = 0, www = 0, hits = 0, longc = 0, stopped = 0; ll maxgap = 0, maxgain = 0; int maxr = 0; long long full = 0;
    ll done_hi = -1;                       /* n already run, as one increasing sweep over the merged windows */
    int SH = argc > 5 ? atoi(argv[4]) : 0, NSH = argc > 5 ? atoi(argv[5]) : 1;
    for (int k = 0; k < ntg; k++) {
        if (k % NSH != SH) continue;
        ll nlo = (tg[k].W - 6) / 2 - HALF, nhi = (tg[k].W - 6) / 2;
        if (nlo <= done_hi) nlo = done_hi + 1;
        ll wcap = tg[k].W;                 /* the largest target width a cycle from this window could need */
        for (int j = k; j < ntg && (tg[j].W - 6) / 2 - HALF <= nhi; j++) if (tg[j].W > wcap) wcap = tg[j].W;
        for (ll n = nlo; n <= nhi; n++) {
            set_start(2 * n + 6); add_mark(tG, 1); add_mark(tM, 2 * n + 4); halted = bad = 0; nend = 0;
            int r = 0; cycles++;
            for (;;) {
                cur_round = ++r; nend = 0; do_round(); rounds++;
                if (halted || bad) { printf("STOP n "); pr(n); printf(" round %d halted %d bad %d\n", r, halted, bad); stopped++; break; }
                if (nm == 2 && MT(1) == tM && realP(1) == realW() - 2) { full++; if (realW() - 2 * n - 6 > maxgain) maxgain = realW() - 2 * n - 6; break; }
                ll w = realW();
                if (nm == 4 && MT(0) == tG && MT(1) == tW && MT(2) == tW && MT(3) == tW) {
                    www++; ll b = realP(2), c = realP(3), R = w - c - 1;
                    if (w - 2 * n > maxgap) maxgap = w - 2 * n;
                    int lo = 0, hi = ntg;          /* binary search on W */
                    while (lo < hi) { int m = (lo + hi) / 2; if (tg[m].W < w) lo = m + 1; else hi = m; }
                    for (int i = lo; i < ntg && tg[i].W == w; i++) if (tg[i].b == b && tg[i].R == R) {
                        hits++; printf("HIT n "); pr(n); printf(" round %d %s a ", r, tg[i].tag); pr(realP(1)); printf("\n");
                    }
                }
                if (w > wcap) break;            /* widths only grow: no target left for this cycle */
                if (r >= MAXR) { longc++; break; }
            }
            if (r > maxr) maxr = r;
        }
        if (nhi > done_hi) done_hi = nhi;
    }
    printf("targets %d half %lld cycles %lld rounds %lld three-wall %lld hits %lld long %lld stopped %lld maxround %d max(W-2n) ",
           ntg, (long long)HALF, cycles, rounds, www, hits, longc, stopped, maxr);
    pr(maxgap); printf(" full-cycles %lld max-cycle-gain ", full); pr(maxgain); printf("\n");
    return 0;
}
