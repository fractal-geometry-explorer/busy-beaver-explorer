/* doucette: iterate Doucette's map F(D) = D + v + 3a, D = 2^v (2a + 1), from D = 6, in plain multi-precision C.
 *
 *   doucette TERMS [EVERY]
 *
 * Space Needle halts iff some term is a power of two (lean/Collatz.lean, halts_iff_pow2).  Prints every EVERY-th
 * term's index, bit length and the largest v seen so far, and stops with "POWER OF TWO" if one is hit.  The first
 * terms are printed in full (decimal, while they fit in 64 bits) to compare with the published 6, 10, 17, 41, ... */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef unsigned __int128 u128;

int main(int argc, char **argv) {
    long long terms = argc > 1 ? atoll(argv[1]) : 1000000, every = argc > 2 ? atoll(argv[2]) : 100000;
    size_t cap = (size_t)(terms / 60 + 64);
    uint64_t *d = calloc(cap, 8), *s = calloc(cap, 8);
    size_t n = 1; d[0] = 6;
    int maxv = 0; long long sumv = 0;
    for (long long k = 0; k < terms; k++) {
        /* power of two? */
        int pc = 0;
        for (size_t i = 0; i < n && pc < 2; i++) pc += __builtin_popcountll(d[i]);
        if (pc == 1) { printf("POWER OF TWO at term %lld\n", k); return 1; }
        if (n == 1 && k < 40) printf("term %lld = %llu\n", k, (unsigned long long)d[0]);
        /* v = trailing zeros */
        size_t z = 0; while (d[z] == 0) z++;
        int v = (int)(64 * z + __builtin_ctzll(d[z]));
        if (v > maxv) maxv = v;
        sumv += v;
        /* s = D >> (v + 1) */
        int sh = v + 1; size_t w = (size_t)sh / 64; int b = sh % 64;
        size_t m = n - w;
        for (size_t i = 0; i < m; i++) {
            uint64_t lo = d[i + w] >> b;
            uint64_t hi = (b && i + w + 1 < n) ? d[i + w + 1] << (64 - b) : 0;
            s[i] = lo | hi;
        }
        while (m > 0 && s[m - 1] == 0) m--;
        /* D += 3 s + v */
        u128 carry = (u128)v;
        for (size_t i = 0; i < n || carry; i++) {
            if (i >= n) { d[n++] = 0; }
            u128 t = (u128)d[i] + carry + (i < m ? (u128)s[i] * 3 : 0);
            d[i] = (uint64_t)t; carry = t >> 64;
            if (i >= m && carry == 0 && i >= n - 1) break;
            if (i + 1 >= cap) { fprintf(stderr, "capacity\n"); return 2; }
        }
        if ((k + 1) % every == 0) {
            int top = 63 - __builtin_clzll(d[n - 1]);
            printf("term %lld: %zu bits, max v so far %d, mean v %.4f\n", k + 1, 64 * (n - 1) + top + 1, maxv, (double)sumv / (k + 1));
            fflush(stdout);
        }
    }
    printf("no power of two in the first %lld terms; largest v = %d\n", terms, maxv);
    return 0;
}
