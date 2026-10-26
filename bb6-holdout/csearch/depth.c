/* D(n): the number of low binary digits a cycle depends on. Smallest k such that n + j*3*2^k gives the same
   increment, the same number of rounds and the same cascade length for several random j. */
#include "model_core.h"
static ll pred(ll d) { return (d % 4 == 2) ? (d - 2) / 2 : d / 2 + 4; }
static int chain_len(void) {
    int best = nend > 0 ? 1 : 0, cur = 1;
    for (int i = 1; i < nend; i++) { if (endd[i] == pred(endd[i-1])) { cur++; if (cur > best) best = cur; } else cur = 1; }
    return best;
}
static void sig(ll n, ll *inc, int *r, int *L) { ll m = cycle(n, r); *inc = m - n; *L = chain_len(); }
static unsigned long long rs = 88172645463325252ULL;
static ll rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (ll)(rs >> 40); }
int D(ll n, int *Lout) {
    ll i0; int r0, L0; sig(n, &i0, &r0, &L0); *Lout = L0;
    for (int k = 1; k <= 40; k++) {
        int ok = 1;
        for (int t = 0; t < 4 && ok; t++) {
            ll j = 1 + (rnd() & 0xFFFF); ll i1; int r1, L1;
            sig(n + j * (3LL << k), &i1, &r1, &L1);
            if (i1 != i0 || r1 != r0 || L1 != L0) ok = 0;
        }
        if (ok) return k;
    }
    return 99;
}
int main(int argc, char **argv) {
    if (argv[1][0] == 'r') {                       /* r lo count : D and L for a run of consecutive n */
        ll lo = atoll(argv[2]), cnt = atoll(argv[3]);
        long long tab[64][64] = {{0}};
        for (ll n = lo; n < lo + cnt; n++) { int L; int d = D(n, &L); if (d > 63) d = 63; if (L > 63) L = 63; tab[L][d]++; }
        for (int L = 0; L < 64; L++) { long long tot = 0, mx = 0; double mean = 0; int dmax = 0;
            for (int d = 0; d < 64; d++) if (tab[L][d]) { tot += tab[L][d]; mean += d * (double)tab[L][d]; dmax = d; }
            if (tot) printf("chain %2d: %9lld cycles, digits depended on: mean %.1f, max %d\n", L, tot, mean / tot, dmax); }
        return 0;
    }
    for (int a = 1; a < argc; a++) { ll n = atoll(argv[a]); int L; int d = D(n, &L); printf("n=%lld chain=%d digits=%d\n", n, L, d); }
    return 0;
}
