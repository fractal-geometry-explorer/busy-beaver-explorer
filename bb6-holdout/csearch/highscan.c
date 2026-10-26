/* Fix an ending r (mod 2^k) and scan the leading part H: n = r + 2^k * H for H = 1..N. */
#include "model_core.h"
static ll pred(ll d) { return (d % 4 == 2) ? (d - 2) / 2 : d / 2 + 4; }
static int chain_len(void) { int best = nend > 0 ? 1 : 0, cur = 1;
    for (int i = 1; i < nend; i++) { if (endd[i] == pred(endd[i-1])) { cur++; if (cur > best) best = cur; } else cur = 1; } return best; }
int main(int argc, char **argv) {
    ll r = atoll(argv[1]); int k = atoi(argv[2]); ll N = atoll(argv[3]); long long hist[64] = {0}; int mx = 0; ll arg = 0;
    for (ll H = 1; H <= N; H++) { ll n = r + (H << k); int rr; ll m = cycle(n, &rr); if (m < 0) { printf("STOP n=%lld\n", n); continue; }
        int L = chain_len(); hist[L]++; if (L > mx) { mx = L; arg = n; printf("  new longest %d at n=%lld (H=%lld)\n", L, n, H); fflush(stdout); } }
    printf("ending %lld (mod 2^%d), H = 1..%lld: cascade lengths", r, k, N);
    for (int i = 0; i < 64; i++) if (hist[i]) printf(" %d:%lld", i, hist[i]); printf("\n");
}
