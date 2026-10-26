/* Cascade lengths for n = 2^v * m - 2 (n + 2 has v trailing zeros), m odd and random, n about 2^S. */
#include "model_core.h"
static ll pred(ll d) { return (d % 4 == 2) ? (d - 2) / 2 : d / 2 + 4; }
static int chain_len(void) { int best = nend > 0 ? 1 : 0, cur = 1;
    for (int i = 1; i < nend; i++) { if (endd[i] == pred(endd[i-1])) { cur++; if (cur > best) best = cur; } else cur = 1; } return best; }
static unsigned long long rs = 1234567;
static unsigned long long rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
int main(int argc, char **argv) {
    int S = atoi(argv[1]); int N = atoi(argv[2]);
    for (int v = 1; v <= S - 6; v += (v < 8 ? 1 : 3)) {
        long long hist[64] = {0}; int mx = 0; ll arg = 0;
        for (int t = 0; t < N; t++) {
            ll m = (ll)(rnd64() >> (64 - (S - v))) | 1 | (1LL << (S - v - 1));
            ll n = (m << v) - 2; int r; cycle(n, &r); int L = chain_len(); hist[L]++; if (L > mx) { mx = L; arg = n; }
        }
        printf("v=%2d: share with cascade >= 3: %.4f, >= 5: %.6f, longest %d (n=%lld)\n", v,
               (double)(N - hist[0] - hist[1] - hist[2]) / N, (double)({long long s=0; for(int i=5;i<64;i++) s+=hist[i]; s;}) / N, mx, arg);
        fflush(stdout);
    }
}
