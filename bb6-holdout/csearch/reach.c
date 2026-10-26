/* Continue the machine's trajectory from n0 until it passes a target; report whether it lands on it,
   and the longest cascade on the way. */
#include "model_core.h"
static ll pred(ll d) { return (d % 4 == 2) ? (d - 2) / 2 : d / 2 + 4; }
static int chain_len(void) { int best = nend > 0 ? 1 : 0, cur = 1;
    for (int i = 1; i < nend; i++) { if (endd[i] == pred(endd[i-1])) { cur++; if (cur > best) best = cur; } else cur = 1; } return best; }
int main(int argc, char **argv) {
    ll n = atoll(argv[1]), target = atoll(argv[2]); ll cycles = 0; int mx = 0; ll arg = 0; ll mod = 1LL << 33, endr = atoll(argv[3]);
    ll family_hits = 0;
    while (n <= target) {
        if (n == target) printf("the trajectory lands on n=%lld\n", n);
        if ((n & (mod - 1)) == endr) { family_hits++; printf("in the 33-digit family: n=%lld\n", n); }
        int r; ll m = cycle(n, &r); int L = chain_len(); if (L > mx) { mx = L; arg = n; }
        if (m <= n) { printf("STOP at %lld\n", n); return 1; }
        n = m; cycles++;
    }
    printf("passed %lld after %lld more cycles; longest cascade on the way %d (n=%lld); family hits %lld\n", target, cycles, mx, arg, family_hits);
}
