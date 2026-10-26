#include "model_core_r.h"
#include <string.h>
/* log2(|L1| / E) at loop pass starts, L1 = 147b + 280E - 392c - 578; also the real-number ratios b/E, c/E. */
static char hist[6000][16]; static double lr[6000]; static double br[6000]; static int gw[6000];
int main(int argc, char **argv) {
    long N = atol(argv[1]); ll start = atoll(argv[2]); unsigned long long s = 0xABCDEF987ULL;
    double mn = 99, mxv = -99, bmin = 9, bmax = -9; long long cnt = 0; long long hist2[40] = {0};
    for (long t = 0; t < N; t++) {
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll n = start + (ll)(s % (unsigned long long)start);
        nm = 0; halted = 0; bad = 0; nend = 0; W = 2 * n + 6; add('G', 1); add('M', W - 2); int nr = 0;
        for (int r = 1; r <= 5000; r++) { CUR_RD = r; do_round(); if (halted || bad) break;
            int idx[MAXM], k = 0; for (int i = 0; i < nm; i++) if (A[i]) idx[k++] = i;
            for (int i = 1; i < k; i++) { int v = idx[i], j = i - 1; while (j >= 0 && P[idx[j]] > P[v]) { idx[j+1] = idx[j]; j--; } idx[j+1] = v; }
            memset(hist[nr], 0, 16); for (int i = 0; i < k && i < 15; i++) hist[nr][i] = T[idx[i]];
            gw[nr] = 0; if (!strcmp(hist[nr], "GWWW")) { double b = P[idx[2]], c = P[idx[3]], E = W; double L1 = 147.0 * b + 280.0 * E - 392.0 * c - 578; lr[nr] = log2(fabs(L1) / E); br[nr] = b / E; gw[nr] = 1; }
            nr++;
            int alive = 0, ok = 0; for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M' && P[i] == W - 2) ok = 1; }
            if (alive == 2 && ok) break; }
        for (int i = 0; i + 2 < nr; i++) if (gw[i] && !strcmp(hist[i+1], "GBW") && !strcmp(hist[i+2], "GMB")) {
            cnt++; if (lr[i] < mn) mn = lr[i]; if (lr[i] > mxv) mxv = lr[i]; if (br[i] < bmin) bmin = br[i]; if (br[i] > bmax) bmax = br[i];
            int b = (int)floor(lr[i]) + 20; if (b < 0) b = 0; if (b > 39) b = 39; hist2[b]++; }
    }
    printf("%lld pass starts: log2(|L1|/E) from %.2f to %.2f; b/E from %.3f to %.3f\n", cnt, mn, mxv, bmin, bmax);
    for (int b = 0; b < 40; b++) if (hist2[b]) printf("  [%d, %d): %lld\n", b - 20, b - 19, hist2[b]);
}
