#include "model_core_r.h"
#include <string.h>
/* Shape transition counts in runs started from random block states G 1, B r, W R. */
#define NS 400
static char shp[NS][12]; static int nsh; static long long tr[NS][NS], tot[NS];
static int sid(const char *s) { for (int i = 0; i < nsh; i++) if (!strcmp(shp[i], s)) return i; if (nsh >= NS) return NS - 1; strcpy(shp[nsh], s); return nsh++; }
int main(int argc, char **argv) {
    unsigned long long s = 0x2545F4914F6CDD1DULL; long N = argc > 1 ? atol(argv[1]) : 2000000;
    sid("start"); sid("end");
    for (long t = 0; t < N; t++) {
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll w = (ll)((s >> 22) | (1ULL << 41)) & ~1LL;
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll D = (ll)(s >> 30) | 1;
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll r = ((ll)(w * 0.3) + (ll)(s >> 44)) & ~1LL;
        ll R = w - D; if (R <= r + 10) continue;
        nm = 0; halted = 0; bad = 0; nend = 0; W = w; add('G', 1); add('B', r); add('W', R);
        int prev = 0;
        for (int rd = 1; rd < 400; rd++) {
            CUR_RD = rd; do_round(); if (halted || bad) break;
            int idx[MAXM], k = 0; for (int i = 0; i < nm; i++) if (A[i]) idx[k++] = i;
            for (int i = 1; i < k; i++) { int v = idx[i], j = i - 1; while (j >= 0 && P[idx[j]] > P[v]) { idx[j+1] = idx[j]; j--; } idx[j+1] = v; }
            char sh[12] = {0}; for (int i = 0; i < k && i < 11; i++) sh[i] = T[idx[i]];
            int ok = 0; for (int i = 0; i < nm; i++) if (A[i] && T[i] == 'M' && P[i] == W - 2) ok = 1;
            int cur = (k == 2 && ok) ? 1 : sid(sh);
            tr[prev][cur]++; tot[prev]++; prev = cur; if (cur == 1) break;
        }
    }
    for (int i = 0; i < nsh; i++) if (tot[i] > 20000) { printf("%-10s (%lld):", shp[i], tot[i]);
        for (int j = 0; j < nsh; j++) if (tr[i][j] * 200 > tot[i]) printf("  %s %.1f%%", shp[j], 100.0 * tr[i][j] / tot[i]); printf("\n"); }
}
