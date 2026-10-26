#include "model_core_r.h"
#include <string.h>
/* Sample n; print n and the round of the first meeting of every right-end run whose first rounds match a given
   shape prefix (stars mark rounds with a run meeting are ignored: only shapes are compared). */
static ll pred(ll d) { return (d % 4 == 2) ? (d - 2) / 2 : d / 2 + 4; }
static char hist[6000][16];
int main(int argc, char **argv) {
    long N = atol(argv[1]); ll start = atoll(argv[2]); int np = argc - 3; long found = 0, want = 400;
    unsigned long long s = 0x1234567ULL;
    for (long t = 0; t < N && found < want; t++) {
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll n = start + (ll)(s >> 22);
        nm = 0; halted = 0; bad = 0; nend = 0; W = 2 * n + 6; add('G', 1); add('M', W - 2); int nr = 0;
        for (int r = 1; r <= 5000; r++) {
            CUR_RD = r; do_round(); if (halted || bad) break;
            int idx[MAXM], k = 0; for (int i = 0; i < nm; i++) if (A[i]) idx[k++] = i;
            for (int i = 1; i < k; i++) { int v = idx[i], j = i - 1; while (j >= 0 && P[idx[j]] > P[v]) { idx[j+1] = idx[j]; j--; } idx[j+1] = v; }
            char *sh = hist[nr]; memset(sh, 0, 16); for (int i = 0; i < k && i < 15; i++) sh[i] = T[idx[i]]; nr++;
            int alive = 0, ok = 0; for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M' && P[i] == W - 2) ok = 1; }
            if (alive == 2 && ok) break;
        }
        /* run starts: meeting i with i == 0 or endd[i] != pred(endd[i-1]) */
        for (int i = 0; i < nend; i++) {
            if (i > 0 && endd[i] == pred(endd[i-1])) continue;
            int r0 = endrd[i]; int okp = 1;
            for (int j = 0; j < np; j++) if (r0 - 1 + j >= nr || strcmp(hist[r0 - 1 + j], argv[3 + j])) { okp = 0; break; }
            if (okp) { int L = 1; while (i + L < nend && endd[i + L] == pred(endd[i + L - 1])) L++; printf("%lld %d %d\n", n, r0, L); found++; break; }
        }
    }
}
