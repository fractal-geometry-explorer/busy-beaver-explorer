/* Jump next(n) - n grouped by v = trailing zeros of n+2, for all n below a limit. */
#include "model_core.h"
int main(int argc, char **argv) {
    ll hi = atoll(argv[1]); int vmax = 12;
    static long long cnt[40][200]; static long long tot[40];
    for (ll n = 2; n < hi; n++) {
        ll m2 = n + 2; int v = 0; while ((m2 & 1) == 0) { m2 >>= 1; v++; }
        if (m2 == 1) continue;
        int r; ll m = cycle(n, &r); ll d = m - n; if (v > 30) v = 30;
        tot[v]++; if (d >= 0 && d < 200) cnt[v][d]++;
    }
    for (int v = 0; v <= vmax; v++) {
        if (!tot[v]) continue;
        printf("v=%2d (%lld n): ", v, tot[v]);
        int shown = 0;
        for (int d = 0; d < 200 && shown < 8; d++) if (cnt[v][d] * 200 > tot[v]) { printf(" +%d:%.1f%%", d, 100.0 * cnt[v][d] / tot[v]); shown++; }
        long long seen = 0; for (int d = 0; d < 200; d++) seen += cnt[v][d] * (cnt[v][d] * 200 > tot[v]);
        printf("  (others %.1f%%)\n", 100.0 * (tot[v] - seen) / tot[v]);
    }
}
