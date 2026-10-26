#include "model_core_r.h"
#include <string.h>
/* print start states (W, r, R) whose first rounds follow a given shape sequence */
int main(int argc, char **argv) {
    int ns = argc - 2; long want = atol(argv[1]); unsigned long long s = 0x9E3779B97F4A7C15ULL; long found = 0;
    for (long t = 0; found < want && t < 2000000000L; t++) {
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll w = (ll)((s >> 30) | (1ULL << 33)) & ~1LL;
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll D = (ll)(s >> 38) | 1;
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll r = ((ll)(w * 0.3) + (ll)(s >> 52)) & ~1LL;
        ll R = w - D; if (R <= r + 10) continue;
        nm = 0; halted = 0; bad = 0; nend = 0; W = w; add('G', 1); add('B', r); add('W', R);
        int okk = 1;
        for (int rd = 0; rd < ns && okk; rd++) {
            CUR_RD = rd + 1; do_round(); if (halted || bad) { okk = 0; break; }
            int idx[MAXM], k = 0; for (int i = 0; i < nm; i++) if (A[i]) idx[k++] = i;
            for (int i = 1; i < k; i++) { int v = idx[i], j = i - 1; while (j >= 0 && P[idx[j]] > P[v]) { idx[j+1] = idx[j]; j--; } idx[j+1] = v; }
            char sh[16] = {0}; for (int i = 0; i < k && i < 15; i++) sh[i] = T[idx[i]];
            if (strcmp(sh, argv[2 + rd])) okk = 0;
        }
        if (okk) { printf("%lld %lld %lld\n", w, r, R); found++; }
    }
}
