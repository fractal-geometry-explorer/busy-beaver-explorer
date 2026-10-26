/* Fast trajectory follower: the jump of each clean tape n is looked up in the table of settled residue classes
   (valid for n >= 2^k because every class up to 44 digits has j_min <= 1); n whose class is still open at the table's
   depth are simulated directly.  Every 2^20 steps one looked-up step is re-simulated as a check.
   Usage: fastfollow classes.txt start_n start_cycles target_n                                                   */
#include "model_core.h"
#include <stdint.h>
#include <string.h>
static ll pred(ll d) { return (d % 4 == 2) ? (d - 2) / 2 : d / 2 + 4; }
static int chain_len(void) {
    int best = nend > 0 ? 1 : 0, cur = 1;
    for (int i = 1; i < nend; i++) { if (endd[i] == pred(endd[i-1])) { cur++; if (cur > best) best = cur; } else cur = 1; }
    return best;
}
#define D0 24
#define DMAX 33
static uint32_t *arr;                       /* residues mod 2^D0: (jump << 8) | chain, 0 = open at D0 */
static uint64_t *hk; static uint32_t *hv; static uint64_t HSZ;   /* deeper classes: key = rho | (k << 40) */
static inline uint64_t hsh(uint64_t x) { x ^= x >> 31; x *= 0x7fb5d329728ea185ULL; x ^= x >> 27; x *= 0x81dadef4bc2dd44dULL; return x ^ (x >> 33); }
static void hput(uint64_t key, uint32_t v) { uint64_t i = hsh(key) & (HSZ - 1); while (hk[i]) { i = (i + 1) & (HSZ - 1); } hk[i] = key; hv[i] = v; }
static uint32_t hget(uint64_t key) { uint64_t i = hsh(key) & (HSZ - 1); while (hk[i]) { if (hk[i] == key) return hv[i]; i = (i + 1) & (HSZ - 1); } return 0; }
static inline uint32_t lookup(ll n) {
    uint32_t v = arr[n & ((1LL << D0) - 1)];
    if (v) return v;
    for (int k = D0 + 1; k <= DMAX; k++) { uint32_t w = hget((uint64_t)(n & ((1LL << k) - 1)) | ((uint64_t)k << 40)); if (w) return w; }
    return 0;
}
int main(int argc, char **argv) {
    arr = calloc(1LL << D0, 4); HSZ = 1ULL << 22; hk = calloc(HSZ, 8); hv = calloc(HSZ, 4);
    FILE *f = fopen(argv[1], "r"); int k; ll rho, jm, jump; int rounds, chain; long long nc = 0;
    while (fscanf(f, "%d %lld %lld %lld %d %d", &k, &rho, &jm, &jump, &rounds, &chain) == 6) {
        if (k > DMAX) continue; uint32_t v = ((uint32_t)jump << 8) | (uint32_t)chain; nc++;
        if (k <= D0) for (ll r = rho; r < (1LL << D0); r += 1LL << k) arr[r] = v; else hput((uint64_t)rho | ((uint64_t)k << 40), v);
    }
    ll n = atoll(argv[2]); long long cyc = atoll(argv[3]); ll target = atoll(argv[4]);
    printf("%lld classes loaded; following from n = %lld (cycle %lld) to %lld\n", nc, n, cyc, target); fflush(stdout);
    long long hist[64] = {0}, direct = 0, checks = 0; int best = 0; ll next_report = (n / 100000000000LL + 1) * 100000000000LL;
    while (n < target) {
        uint32_t v = lookup(n); ll j; int c;
        if (v) {
            j = v >> 8; c = v & 255;
            if ((cyc & ((1 << 20) - 1)) == 0) {           /* check */
                int r; ll nx = cycle(n, &r); checks++;
                if (nx - n != j || chain_len() != c) { printf("CHECK FAILED at n = %lld: table %lld/%d, direct %lld/%d\n", n, j, c, nx - n, chain_len()); return 1; }
            }
        } else {
            int r; ll nx = cycle(n, &r); direct++;
            if (nx < 0) { printf("n = %lld: %s\n", n, nx == -1 ? "HALT" : "bad / too long"); return 1; }
            j = nx - n; c = chain_len();
        }
        if (c > 63) c = 63; hist[c]++;
        if (c >= 10) { printf("  n = %lld (cycle %lld): chain %d\n", n, cyc, c); fflush(stdout); }
        if (c > best) best = c;
        n += j; cyc++;
        if (n >= next_report) {
            printf("reached n = %lld after %lld cycles; simulated directly %lld, checks %lld (all passed); chain counts:", n, cyc, direct, checks);
            for (int i = 0; i < 64; i++) if (hist[i]) printf(" %d:%lld", i, hist[i]);
            printf("\n"); fflush(stdout); next_report += 100000000000LL;
        }
    }
    printf("final: n = %lld after %lld cycles; simulated directly %lld; checks %lld passed; longest chain %d; chain counts:", n, cyc, direct, checks, best);
    for (int i = 0; i < 64; i++) if (hist[i]) printf(" %d:%lld", i, hist[i]);
    printf("\n");
    return 0;
}
