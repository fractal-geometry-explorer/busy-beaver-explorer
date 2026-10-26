#include "model_core_r.h"
#include <string.h>
/* At G-B-W rounds with v2(r) = 1: which next shapes occur, and how they depend on residues of r, R, W. */
static int v2(ll x) { int c = 0; while (x && !(x & 1) && c < 39) { x >>= 1; c++; } return c; }
static char shp[64][8]; static long long shc[64]; static int nsh;
static long long resd[3][64][2];   /* [which quantity][value mod 64][next is GWWW] */
int main(void) {
    unsigned long long s = 0x2545F4914F6CDD1DULL;
    for (long t = 0; t < 3000000; t++) {
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll w = (ll)((s >> 22) | (1ULL << 41)) & ~1LL;
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll D = (ll)(s >> 30) | 1;
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll r = ((ll)(w * 0.3) + (ll)(s >> 44)) & ~1LL;
        ll R = w - D; if (R <= r + 10) continue;
        nm = 0; halted = 0; bad = 0; nend = 0; W = w; add('G', 1); add('B', r); add('W', R);
        int pend = 0; ll pr = 0, pR = 0, pW = 0;
        for (int rd = 1; rd < 200; rd++) {
            CUR_RD = rd; do_round(); if (halted || bad) break;
            int idx[MAXM], k = 0; for (int i = 0; i < nm; i++) if (A[i]) idx[k++] = i;
            for (int i = 1; i < k; i++) { int v = idx[i], j = i - 1; while (j >= 0 && P[idx[j]] > P[v]) { idx[j+1] = idx[j]; j--; } idx[j+1] = v; }
            char sh[8] = {0}; for (int i = 0; i < k && i < 7; i++) sh[i] = T[idx[i]];
            if (pend) { int f = -1; for (int i = 0; i < nsh; i++) if (!strcmp(shp[i], sh)) f = i; if (f < 0 && nsh < 64) { f = nsh++; strcpy(shp[f], sh); } if (f >= 0) shc[f]++;
                int g = (k == 4 && !strcmp(sh, "GWWW"));
                resd[0][(pR - pr) & 63][g]++; resd[1][(pW - pR) & 63][g]++; resd[2][pr & 63][g]++; pend = 0; }
            if (k == 3 && sh[1] == 'B' && sh[2] == 'W' && v2(P[idx[1]]) == 1) { pend = 1; pr = P[idx[1]]; pR = P[idx[2]]; pW = W; }
            int ok = 0; for (int i = 0; i < nm; i++) if (A[i] && T[i] == 'M' && P[i] == W - 2) ok = 1;
            if (k == 2 && ok) break;
        }
    }
    printf("next shapes after G-B-W with v2(r) = 1:\n"); for (int i = 0; i < nsh; i++) printf("  %-8s %lld\n", shp[i], shc[i]);
    const char *nm3[3] = {"R - r", "W - R", "r"};
    for (int q = 0; q < 3; q++) { printf("%s mod 64 -> share leading to three walls:\n ", nm3[q]);
        for (int v = 0; v < 64; v++) { long long a = resd[q][v][1], b = resd[q][v][0]; if (a + b) printf(" %d:%.0f%%", v, 100.0 * a / (a + b)); } printf("\n"); }
}
