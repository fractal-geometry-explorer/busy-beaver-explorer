/* Longest cascade and rounds per trailing-zero class v of n+2 (random odd parts, n about 2^S). */
#include "model_core.h"
static ll pred(ll d) { return (d % 4 == 2) ? (d - 2) / 2 : d / 2 + 4; }
static int chain_len(void) { int best = nend > 0 ? 1 : 0, cur = 1;
    for (int i = 1; i < nend; i++) { if (endd[i] == pred(endd[i-1])) { cur++; if (cur > best) best = cur; } else cur = 1; } return best; }
static unsigned long long rs = 0x2545F4914F6CDD1DULL;
static unsigned long long rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
int main(int argc, char **argv) {
    int S = atoi(argv[1]), N = atoi(argv[2]);
    for (int v = 0; v <= 30; v++) {
        int mxL = 0, mnR = 1 << 30, mxR = 0; long long c5 = 0;
        for (int t = 0; t < N; t++) {
            ll m = (ll)(rnd64() >> (64 - (S - v))) | 1 | (1LL << (S - v - 1));
            ll n = (m << v) - 2; int r; cycle(n, &r); int L = chain_len();
            if (L > mxL) mxL = L; if (L >= 5) c5++; if (r < mnR) mnR = r; if (r > mxR) mxR = r;
        }
        printf("v=%2d: rounds %d..%d, longest cascade %d, share with 5+ meetings %.5f\n", v, mnR, mxR, mxL, (double)c5 / N);
    }
}
