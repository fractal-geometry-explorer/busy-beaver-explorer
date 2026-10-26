#include "model_core_r.h"
/* Over many n: the distribution of the halvings log2(W0/(d+2)) at the first meeting of each right-end run,
   and the largest seen. */
static ll pred(ll d) { return (d % 4 == 2) ? (d - 2) / 2 : d / 2 + 4; }
int main(int argc, char **argv) {
    long N = atol(argv[1]); ll start = atoll(argv[2]); int mode = atoi(argv[3]);
    unsigned long long s = 0x5DEECE66DULL; long long hist[200] = {0}; double best = 0; ll bestn = 0; long long tot = 0;
    for (long t = 0; t < N; t++) {
        ll n; if (mode == 2) { if (scanf("%lld", &n) != 1) break; } else { s ^= s << 13; s ^= s >> 7; s ^= s << 17; n = start + (ll)(s % (unsigned long long)start); }
        nm = 0; halted = 0; bad = 0; nend = 0; W = 2 * n + 6; add('G', 1); add('M', W - 2); ll W0 = W;
        for (int r = 1; r <= 5000; r++) { CUR_RD = r; do_round(); if (halted || bad) break;
            int alive = 0, ok = 0; for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M' && P[i] == W - 2) ok = 1; }
            if (alive == 2 && ok) break; }
        for (int i = 0; i < nend; i++) {
            if (i > 0 && endd[i] == pred(endd[i-1])) continue;
            double h = log2((double)W0 / (endd[i] + 2)); int b = (int)(h * 10); if (b < 0) b = 0; if (b > 199) b = 199; hist[b]++; tot++;
            if (h > best) { best = h; bestn = n; }
        }
    }
    printf("%lld run starts; largest starting halvings %.3f (n = %lld)\n", tot, best, bestn);
    for (int b = 0; b < 200; b++) if (hist[b]) printf("  %.1f-%.1f: %lld\n", b / 10.0, (b + 1) / 10.0, hist[b]);
}
