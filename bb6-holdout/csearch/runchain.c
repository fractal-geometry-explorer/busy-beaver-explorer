#include "model_core_r.h"
/* Joint statistics of (halvings where a run ended, halvings where the next run starts). */
static ll pred(ll d) { return (d % 4 == 2) ? (d - 2) / 2 : d / 2 + 4; }
int main(int argc, char **argv) {
    long N = atol(argv[1]); ll start = atoll(argv[2]); int mode = atoi(argv[3]); unsigned long long s = 0xC0FFEE123ULL;
    static double mx[64]; static long long cnt[64]; static double mxgain = -99; ll gn = 0;
    for (long t = 0; t < N; t++) {
        ll n; if (mode == 2) { if (scanf("%lld", &n) != 1) break; } else { s ^= s << 13; s ^= s >> 7; s ^= s << 17; n = start + (ll)(s % (unsigned long long)start); }
        nm = 0; halted = 0; bad = 0; nend = 0; W = 2 * n + 6; add('G', 1); add('M', W - 2); ll W0 = W;
        for (int r = 1; r <= 5000; r++) { CUR_RD = r; do_round(); if (halted || bad) break;
            int alive = 0, ok = 0; for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M' && P[i] == W - 2) ok = 1; }
            if (alive == 2 && ok) break; }
        double prev = -1; int i = 0;
        while (i < nend) {
            int j = i + 1; while (j < nend && endd[j] == pred(endd[j-1])) j++;
            double h0 = log2((double)W0 / (endd[i] + 2)), h1 = log2((double)W0 / (endd[j-1] + 2));
            if (prev >= 0) { int b = (int)prev; if (b > 63) b = 63; cnt[b]++; if (h0 > mx[b]) mx[b] = h0; }
            prev = h1; i = j;
        }
    }
    printf("previous run ended at (halvings) -> largest start of the next run\n");
    for (int b = 0; b < 64; b++) if (cnt[b]) printf("  %2d-%2d: %10lld runs, next start at most %.2f\n", b, b + 1, cnt[b], mx[b]);
}
