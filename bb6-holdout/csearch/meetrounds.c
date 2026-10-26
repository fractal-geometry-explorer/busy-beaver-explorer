#include "model_core_r.h"
static ll pred(ll d) { return (d % 4 == 2) ? (d - 2) / 2 : d / 2 + 4; }
int main(int argc, char **argv) {
    unsigned long long s = 88172645463325252ULL; int want = atoi(argv[1]), shown = 0; int v2want = atoi(argv[2]);
    for (long t = 0; t < 200000000 && shown < 4; t++) {
        s ^= s << 13; s ^= s >> 7; s ^= s << 17;
        ll n = (ll)(s >> 20) | (1LL << 43);
        int v = 0; ll x = n + 2; while (!(x & 1)) { x >>= 1; v++; }
        if (v2want >= 0 && v != v2want) continue;
        int r; cycle(n, &r);
        int best = nend > 0 ? 1 : 0, cur = 1, bs = 0, st = 0;
        for (int i = 1; i < nend; i++) { if (endd[i] == pred(endd[i-1])) { cur++; if (cur > best) { best = cur; bs = st; } } else { cur = 1; st = i; } }
        if (best != want) continue;
        shown++; printf("n=%lld v2(n+2)=%d rounds=%d chain %d at rounds:", n, v, r, best);
        for (int i = bs; i < bs + best; i++) printf(" %d", endrd[i]); printf("\n");
    }
}
