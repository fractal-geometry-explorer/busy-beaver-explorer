/* The trajectory modulo 2^K as an orbit of the finite map T(r) = r + J(r) mod 2^K.
   J(r) comes from the settled classes (file: k rho jmin jump rounds chain), 0 where the class is still open.
   Runs the machine's trajectory (clean tapes from n = 2) and compares it with T. */
#include "model_core.h"
#include <string.h>
#include <stdint.h>
int main(int argc, char **argv) {
    int K = atoi(argv[1]); ll laps = atoll(argv[3]); ll M = 1LL << K;
    uint16_t *J = calloc(M, 2); uint8_t *CH = calloc(M, 1);
    FILE *f = fopen(argv[2], "r"); int k; ll rho, jm, jump; int rounds, chain; long long ncls = 0;
    while (fscanf(f, "%d %lld %lld %lld %d %d", &k, &rho, &jm, &jump, &rounds, &chain) == 6) {
        if (k > K) continue; ncls++;
        for (ll r = rho; r < M; r += 1LL << k) { J[r] = (uint16_t)jump; CH[r] = (uint8_t)chain; }
    }
    long long open = 0; for (ll r = 0; r < M; r++) if (!J[r]) open++;
    printf("K=%d: %lld settled classes, %lld residues of %lld still open (%.4f%%)\n", K, ncls, open, M, 100.0 * open / M);
    /* trajectory */
    ll n = 2; int rd; ll start = 3 * M;              /* compare once n > 3*2^K (well past the small cases) */
    uint8_t *seen = calloc(M, 1); long long steps = 0, agree = 0, atopen = 0, mism = 0, lap = -1, lapcount = 0;
    long long prevlap_n = 0, shared = 0, lapsize = 0, prevsize = 0;
    uint8_t *prevlap = calloc(M, 1), *curlap = calloc(M, 1);
    int maxch_traj = 0;
    while (1) {
        ll nx = cycle(n, &rd); if (nx < 0) { printf("halt/bad at n=%lld\n", n); return 1; }
        if (n > start) {
            ll r = n & (M - 1);
            if (J[r]) { if (nx - n == J[r]) agree++; else mism++; } else atopen++;
            steps++;
            ll L = n / (3 * M);
            if (L != lap) {
                if (lap >= 0) {
                    long long sh = 0; for (ll i = 0; i < M; i++) if (curlap[i] && prevlap[i]) sh++;
                    if (lapcount > 0) printf("lap %lld: %lld residues visited, %.2f%% shared with the previous lap\n", lap, lapsize, 100.0 * sh / (lapsize ? lapsize : 1));
                    memcpy(prevlap, curlap, M); memset(curlap, 0, M); prevsize = lapsize; lapsize = 0; lapcount++;
                    if (lapcount > laps) break;
                }
                lap = L;
            }
            if (!curlap[r]) { curlap[r] = 1; lapsize++; }
        }
        n = nx;
    }
    printf("steps compared %lld: jump predicted by the class table %lld times (all correct: %s), at open residues %lld\n", steps, agree, mism ? "NO" : "yes", atopen);
    /* the map T: follow it from the last trajectory residue and find its cycle */
    ll r = n & (M - 1); ll *pos = malloc(sizeof(ll) * 4000000); int *idx = calloc(M, sizeof(int)); memset(idx, 0xff, M * sizeof(int));
    int t = 0; while (t < 4000000 && J[r] && idx[r] < 0) { idx[r] = t; pos[t++] = r; r = (r + J[r]) & (M - 1); }
    if (!J[r]) printf("following T from the last residue hits an open residue after %d steps\n", t);
    else if (idx[r] >= 0) {
        int c0 = idx[r], clen = t - c0; long long wsum = 0; int chmax = 0; long long onlap = 0;
        for (int i = c0; i < t; i++) { wsum += J[pos[i]]; if (CH[pos[i]] > chmax) chmax = CH[pos[i]]; if (prevlap[pos[i]]) onlap++; }
        printf("T reaches a cycle after %d steps: length %d, winding %lld (sum of jumps / 2^K), longest chain on it %d; %.2f%% of its residues were visited in the last lap\n",
               c0, clen, wsum / M, chmax, 100.0 * onlap / clen);
    }
    return 0;
}
