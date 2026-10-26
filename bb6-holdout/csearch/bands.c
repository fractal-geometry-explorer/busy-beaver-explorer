/* For each bit length b: the longest cascade over all n with b binary digits, and how many reach 5+, 7+. */
#include "model_core.h"
static ll pred(ll d) { return (d % 4 == 2) ? (d - 2) / 2 : d / 2 + 4; }
static int chain_len(void) {
    int best = nend > 0 ? 1 : 0, cur = 1;
    for (int i = 1; i < nend; i++) { if (endd[i] == pred(endd[i-1])) { cur++; if (cur > best) best = cur; } else cur = 1; }
    return best;
}
int main(int argc, char **argv) {
    int b0 = atoi(argv[1]), b1 = atoi(argv[2]);
    for (int b = b0; b <= b1; b++) {
        ll lo = 1LL << b, hi = 1LL << (b + 1); int mx = 0; ll arg = 0, c5 = 0, c7 = 0;
        for (ll n = lo; n < hi; n++) { int r; cycle(n, &r); int L = chain_len();
            if (L > mx) { mx = L; arg = n; } if (L >= 5) c5++; if (L >= 7) c7++; }
        printf("b=%2d  longest cascade %2d (n=%lld)  reaching 5+: %lld  reaching 7+: %lld\n", b, mx, arg, c5, c7); fflush(stdout);
    }
    return 0;
}
