/* Image of the residue map T(r) = r + J(r) mod 2^K (settled residues only) and its iterates. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef long long ll;
int main(int argc, char **argv) {
    int K = atoi(argv[1]); ll M = 1LL << K;
    uint16_t *J = calloc(M, 2);
    FILE *f = fopen(argv[2], "r"); int k; ll rho, jm, jump; int rounds, chain;
    while (fscanf(f, "%d %lld %lld %lld %d %d", &k, &rho, &jm, &jump, &rounds, &chain) == 6)
        if (k <= K) for (ll r = rho; r < M; r += 1LL << k) J[r] = (uint16_t)jump;
    long long open = 0; for (ll r = 0; r < M; r++) if (!J[r]) open++;
    uint8_t *S = malloc(M), *N = malloc(M); memset(S, 1, M);
    for (int it = 1; it <= 40; it++) {
        memset(N, 0, M);
        for (ll r = 0; r < M; r++) if (S[r] && J[r]) N[(r + J[r]) & (M - 1)] = 1;
        long long c = 0; for (ll r = 0; r < M; r++) c += N[r];
        if (it <= 6 || it % 8 == 0) printf("K=%d: residues reachable in %d steps from settled residues: %lld (%.2f%%)\n", K, it, c, 100.0 * c / M);
        memcpy(S, N, M);
    }
    printf("(%lld open residues, %.3f%%, left out: their jumps depend on higher digits)\n", open, 100.0 * open / M);
}
