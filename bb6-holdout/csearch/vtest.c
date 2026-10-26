/* For n + 2 = 2^v * m (m odd, random, n about 2^S): is the jump fixed, and does it match 3*(floor(3v/5)+2)? */
#include "model_core.h"
static unsigned long long rs = 0x5851F42D4C957F2DULL;
static unsigned long long rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
int main(int argc, char **argv) {
    int S = atoi(argv[1]), N = atoi(argv[2]);
    for (int v = 0; v <= S - 8; v++) {
        long long seen[400] = {0}; int distinct = 0, mn = 1 << 30, mx = 0;
        for (int t = 0; t < N; t++) {
            ll m = (ll)(rnd64() >> (64 - (S - v))) | 1 | (1LL << (S - v - 1));
            ll n = (m << v) - 2; int r; ll nx = cycle(n, &r); ll d = nx - n;
            if (d < 400 && d >= 0) { if (!seen[d]) distinct++; seen[d]++; } if (d < mn) mn = d; if (d > mx) mx = d;
        }
        int pred = 3 * ((3 * v) / 5 + 2);
        int fixed = (distinct == 1);
        printf("v=%2d (v mod 5 = %d): %s", v, v % 5, fixed ? "fixed jump " : "varies, min ");
        printf("+%d", mn); if (!fixed) printf(" .. max +%d", mx);
        if (v % 5 == 1 || v % 5 == 3) printf("   predicted +%d %s", pred, (fixed && mn == pred) ? "✓" : "✗");
        printf("\n");
    }
}
