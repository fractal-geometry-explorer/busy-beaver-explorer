#include "model_core_r.h"
static ll pred(ll d) { return (d % 4 == 2) ? (d - 2) / 2 : d / 2 + 4; }
static char shape[400][64]; static ll lastD[400];
static int run(ll r, ll R, ll w0, int verbose) {
    nm = 0; halted = 0; bad = 0; nend = 0; W = w0;
    add('G', 1); add('B', r); add('W', R);
    int rd;
    for (rd = 1; rd < 300; rd++) {
        CUR_RD = rd; do_round(); if (halted || bad) return -1;
        int idx[MAXM], k = 0; for (int i = 0; i < nm; i++) if (A[i]) idx[k++] = i;
        for (int i = 1; i < k; i++) { int v = idx[i], j = i - 1; while (j >= 0 && P[idx[j]] > P[v]) { idx[j+1] = idx[j]; j--; } idx[j+1] = v; }
        int o = 0; for (int i = 0; i < k && o < 60; i++) shape[rd][o++] = T[idx[i]]; shape[rd][o] = 0;
        int alive = k, ok = 0; for (int i = 0; i < nm; i++) if (A[i] && T[i] == 'M' && P[i] == W - 2) ok = 1;
        if (alive == 2 && ok) break;
    }
    int best = nend > 0 ? 1 : 0, cur = 1, bs = 0, st = 0;
    for (int i = 1; i < nend; i++) { if (endd[i] == pred(endd[i-1])) { cur++; if (cur > best) { best = cur; bs = st; } } else { cur = 1; st = i; } }
    if (verbose) {
        printf("chain %d; meetings at rounds:", best); for (int i = bs; i < bs + best; i++) printf(" %d", endrd[i]); printf("\n   round shapes:");
        int last = endrd[bs + best - 1] + 2; for (int q = 1; q <= last && q < rd; q++) printf(" %d:%s", q, shape[q]); printf("\n");
    }
    return best;
}
int main(int argc, char **argv) {
    unsigned long long s = 0x9E3779B97F4A7C15ULL; int want = atoi(argv[1]), shown = 0;
    for (long t = 0; t < 400000000 && shown < 3; t++) {
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll w = (ll)((s >> 22) | (1ULL << 41)) & ~1LL;
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll D = (ll)(s >> 30) | 1;  /* right wall distance, odd */
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll r = ((ll)(w * 0.3) + (ll)(s >> 44)) & ~1LL;
        ll R = w - D; if (R <= r + 10) continue;
        int c = run(r, R, w, 0);
        if (c >= want) { shown++; run(r, R, w, 1); }
    }
}
