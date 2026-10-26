/* Build n digit by digit (from the last binary digit up) to make the right-end cascade long.
   A partial ending r (n mod 2^k) is scored by the cascade length of several random n of size ~2^S that end in r:
   score = the shortest of those cascades (what the fixed digits guarantee), ties broken by the average. */
#include "model_core.h"
#include <string.h>
static ll pred(ll d) { return (d % 4 == 2) ? (d - 2) / 2 : d / 2 + 4; }
static int chain_len(void) {
    int best = nend > 0 ? 1 : 0, cur = 1;
    for (int i = 1; i < nend; i++) { if (endd[i] == pred(endd[i-1])) { cur++; if (cur > best) best = cur; } else cur = 1; }
    return best;
}
static unsigned long long rs = 0x9E3779B97F4A7C15ULL;

static unsigned long long rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
typedef struct { ll r; int mn; double avg; ll bestn; int bestL; double hmin, havg, hbest; ll hn; } Cand;
static int cmp(const void *a, const void *b) { const Cand *x = a, *y = b;
    if (x->havg != y->havg) return y->havg > x->havg ? 1 : -1; if (x->hmin != y->hmin) return y->hmin > x->hmin ? 1 : -1; return 0; }
static int DIV = 1000000;
static int select_div(Cand *c, int n, int B, int k) {      /* keep the best, at most DIV per ending mod 2^(k-6) */
    if (k < 12) return n < B ? n : B;
    int out = 0; ll mask = (1LL << (k - 6)) - 1;
    /* simple hash table of ending counts */
    int HS = 1 << 22; static ll *keys = 0; static int *cnt = 0;
    if (!keys) { keys = malloc(sizeof(ll) * HS); cnt = malloc(sizeof(int) * HS); }
    memset(cnt, 0, sizeof(int) * HS);
    for (int i = 0; i < n && out < B; i++) {
        ll key = c[i].r & mask; unsigned h = (unsigned)((key * 0x9E3779B97F4A7C15ULL) >> 42) & (HS - 1);
        while (cnt[h] && keys[h] != key) h = (h + 1) & (HS - 1);
        if (cnt[h] >= DIV) continue;
        keys[h] = key; cnt[h]++; c[out++] = c[i];
    }
    return out;
}
int S, NT, MOD3;
static void score(Cand *c, int k) {
    int mn = 1000; double sum = 0; ll step = (MOD3 ? 3LL : 1LL) << k; double hmn = 1e9, hs = 0;
    for (int t = 0; t < NT; t++) {
        ll lo = 1LL << S; ll X = (ll)(rnd64() % (unsigned long long)((lo / step) > 1 ? lo / step : 1)) + lo / step;
        ll n = c->r + step * X; int r; cycle(n, &r); int L = chain_len();
        if (L < mn) mn = L; sum += L; if (L > c->bestL) { c->bestL = L; c->bestn = n; }
        ll md = -1; for (int i = 1; i < nend; i++) if (md < 0 || endd[i] < md) md = endd[i];
        double h = md > 0 ? log2((double)(2 * n + 6) / md) : 0; if (h < hmn) hmn = h; hs += h;
        if (h > c->hbest) { c->hbest = h; c->hn = n; }
    }
    c->mn = mn; c->avg = sum / NT; c->hmin = hmn; c->havg = hs / NT;
}
int main(int argc, char **argv) {
    S = atoi(argv[1]); int B = atoi(argv[2]); NT = atoi(argv[3]); int K = atoi(argv[4]); MOD3 = argc > 5 ? atoi(argv[5]) : 0;
    int k0 = 10; ll M0 = 1LL << k0;
    Cand *beam = malloc(sizeof(Cand) * (size_t)(2 * B + M0 * 3)); int nb = 0;
    for (ll r = 0; r < M0; r++) {
        ll rr = MOD3 ? (r * 3 + 2) % (3 * M0) : r;             /* with MOD3, residues mod 3*2^k that are 2 mod 3 */
        if (MOD3) { rr = r; while (rr % 3 != 2) rr += M0; }     /* CRT: rr ≡ r (mod 2^k), rr ≡ 2 (mod 3) */
        beam[nb].r = rr; beam[nb].bestL = 0; beam[nb].bestn = 0; beam[nb].hbest = 0; beam[nb].hn = 0; score(&beam[nb], k0); nb++;
    }
    qsort(beam, nb, sizeof(Cand), cmp); if (nb > B) nb = B;
    int globalL = 0; ll globaln = 0; double globalH = 0; ll globalHn = 0;
    for (int k = k0; k < K; k++) {
        Cand *nxt = malloc(sizeof(Cand) * (size_t)(2 * nb)); int nn = 0;
        ll step = (MOD3 ? 3LL : 1LL) << k;
        for (int i = 0; i < nb; i++) for (int bit = 0; bit < 2; bit++) {
            Cand c; c.r = beam[i].r + (bit ? step : 0); c.bestL = 0; c.bestn = 0; c.hbest = 0; c.hn = 0; score(&c, k + 1); nxt[nn++] = c;
            if (c.bestL > globalL) { globalL = c.bestL; globaln = c.bestn; }
            if (c.hbest > globalH) { globalH = c.hbest; globalHn = c.hn; }
        }
        qsort(nxt, nn, sizeof(Cand), cmp); nn = select_div(nxt, nn, B, k + 1);
        memcpy(beam, nxt, sizeof(Cand) * nn); nb = nn; free(nxt);
        int bm = 0; for (int i = 0; i < nb; i++) if (beam[i].mn > bm) bm = beam[i].mn;
        printf("digits %2d: guaranteed halvings %.2f; deepest seen %.2f halvings (n=%lld); longest chain seen %d (n=%lld)\n",
               k + 1, beam[0].hmin, globalH, globalHn, globalL, globaln); fflush(stdout);
    }
    return 0;
}
