/* Histogram of right-end cascade chain lengths over a range of n (mark model), printed at the end. */
#include "model_core.h"
static ll pred(ll d) { return (d % 4 == 2) ? (d - 2) / 2 : d / 2 + 4; }
static int chain_len(void) {
    int best = nend > 0 ? 1 : 0, cur = 1;
    for (int i = 1; i < nend; i++) { if (endd[i] == pred(endd[i-1])) { cur++; if (cur > best) best = cur; } else cur = 1; }
    return best;
}
int main(int argc, char **argv) {
    ll lo = atoll(argv[1]), hi = atoll(argv[2]); long long hist[64] = {0};
    for (ll n = lo; n < hi; n++) {
        int r; ll m = cycle(n, &r);
        if (m < 0) { printf("STOP n=%lld code %lld\n", n, m); fflush(stdout); }
        int L = chain_len(); if (L > 63) L = 63; hist[L]++;
        if (L >= 11) { printf("long n=%lld chain=%d\n", n, L); fflush(stdout); }
    }
    printf("range %lld %lld\n", lo, hi);
    for (int i = 0; i < 64; i++) if (hist[i]) printf("%d %lld\n", i, hist[i]);
    return 0;
}
