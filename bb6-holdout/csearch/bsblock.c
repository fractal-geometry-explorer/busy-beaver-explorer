#include "model_core_r.h"
/* For random block states: at each round whose marks are exactly G, B r, W R, record v2(r) and the next round's shape. */
static long long tab[3][40];   /* next shape: 0 = GMB..., 1 = GWWW..., 2 = other */
static int v2(ll x) { int c = 0; while (x && !(x & 1) && c < 39) { x >>= 1; c++; } return c; }
int main(void) {
    unsigned long long s = 0x2545F4914F6CDD1DULL;
    for (long t = 0; t < 3000000; t++) {
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll w = (ll)((s >> 22) | (1ULL << 41)) & ~1LL;
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll D = (ll)(s >> 30) | 1;
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll r = ((ll)(w * 0.3) + (ll)(s >> 44)) & ~1LL;
        ll R = w - D; if (R <= r + 10) continue;
        nm = 0; halted = 0; bad = 0; nend = 0; W = w; add('G', 1); add('B', r); add('W', R);
        int pend = -1; ll prv = 0;
        for (int rd = 1; rd < 200; rd++) {
            CUR_RD = rd; do_round(); if (halted || bad) break;
            int idx[MAXM], k = 0; for (int i = 0; i < nm; i++) if (A[i]) idx[k++] = i;
            for (int i = 1; i < k; i++) { int v = idx[i], j = i - 1; while (j >= 0 && P[idx[j]] > P[v]) { idx[j+1] = idx[j]; j--; } idx[j+1] = v; }
            char sh[8] = {0}; for (int i = 0; i < k && i < 7; i++) sh[i] = T[idx[i]];
            if (pend >= 0) { int nxt = (sh[1] == 'M') ? 0 : (k == 4 && sh[1] == 'W' && sh[2] == 'W' && sh[3] == 'W') ? 1 : 2; tab[nxt][pend]++; pend = -1; }
            if (k == 3 && sh[1] == 'B' && sh[2] == 'W') { pend = v2(P[idx[1]]); }
            int ok = 0; for (int i = 0; i < nm; i++) if (A[i] && T[i] == 'M' && P[i] == W - 2) ok = 1;
            if (k == 2 && ok) break;
        }
    }
    printf("v2(r) at a G-B-W round   next round starts a marker phase   next is three walls (wall step)   other\n");
    for (int v = 1; v < 16; v++) { long long a = tab[0][v], b = tab[1][v], c = tab[2][v], tt = a + b + c; if (!tt) continue;
        printf("   %2d                          %6.1f%%                            %6.1f%%                    %6.1f%%   (%lld)\n", v, 100.0*a/tt, 100.0*b/tt, 100.0*c/tt, tt); }
}
