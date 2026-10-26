#include "model_core_r.h"
#include <string.h>
/* Run starts with more than 2.5 halvings: shape before, round, previous run length and its last halvings. */
static ll pred(ll d) { return (d % 4 == 2) ? (d - 2) / 2 : d / 2 + 4; }
static char shp[6000][16];
int main(int argc, char **argv) {
    long N = atol(argv[1]); ll start = atoll(argv[2]); unsigned long long s = 0x5DEECE66DULL; int shown = 0;
    for (long t = 0; t < N && shown < 25; t++) {
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll n = start + (ll)(s % (unsigned long long)start);
        nm = 0; halted = 0; bad = 0; nend = 0; W = 2 * n + 6; add('G', 1); add('M', W - 2); ll W0 = W; int nr = 0;
        for (int r = 1; r <= 5000; r++) { CUR_RD = r; do_round(); if (halted || bad) break;
            int idx[MAXM], k = 0; for (int i = 0; i < nm; i++) if (A[i]) idx[k++] = i;
            for (int i = 1; i < k; i++) { int v = idx[i], j = i - 1; while (j >= 0 && P[idx[j]] > P[v]) { idx[j+1] = idx[j]; j--; } idx[j+1] = v; }
            nr++; memset(shp[nr], 0, 16); for (int i = 0; i < k && i < 15; i++) shp[nr][i] = T[idx[i]];
            int alive = 0, ok = 0; for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M' && P[i] == W - 2) ok = 1; }
            if (alive == 2 && ok) break; }
        int prevlen = 0; double prevlast = 0; int i = 0;
        while (i < nend) {
            int j = i + 1; while (j < nend && endd[j] == pred(endd[j-1])) j++;
            double h = log2((double)W0 / (endd[i] + 2));
            if (h > 2.5) { printf("n = %lld: run start at round %d, %.2f halvings, shapes before/at: %s -> %s; previous run %d meetings ending at %.2f; this run %d\n",
                n, endrd[i], h, shp[endrd[i] - 1], shp[endrd[i]], prevlen, prevlast, j - i); shown++; }
            prevlen = j - i; prevlast = log2((double)W0 / (endd[j-1] + 2)); i = j;
        }
    }
}
