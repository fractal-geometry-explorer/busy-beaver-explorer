#include "model_core_r.h"
/* At every round with a right-end meeting: the smallest mark position other than the gap at 1, and the smallest gap
   between neighbouring marks, relative to the tape width; and the largest number of marks at any round. */
static ll pred(ll d) { return (d % 4 == 2) ? (d - 2) / 2 : d / 2 + 4; }
int main(int argc, char **argv) {
    long N = atol(argv[1]); ll start = atoll(argv[2]); unsigned long long s = 0x123456789ULL;
    ll minpos = 1LL << 62, minsep = 1LL << 62; ll mpn = 0, msn = 0; int maxm = 0; double minrel = 1;
    for (long t = 0; t < N; t++) {
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll n = start + (ll)(s % (unsigned long long)start);
        nm = 0; halted = 0; bad = 0; nend = 0; W = 2 * n + 6; add('G', 1); add('M', W - 2);
        for (int r = 1; r <= 5000; r++) { int ne0 = nend; CUR_RD = r; do_round(); if (halted || bad) break;
            int idx[MAXM], k = 0; for (int i = 0; i < nm; i++) if (A[i]) idx[k++] = i;
            if (k > maxm) maxm = k;
            for (int i = 1; i < k; i++) { int v = idx[i], j = i - 1; while (j >= 0 && P[idx[j]] > P[v]) { idx[j+1] = idx[j]; j--; } idx[j+1] = v; }
            if (nend > ne0 && r > 1) {
                if (k > 1 && P[idx[1]] < minpos) { minpos = P[idx[1]]; mpn = n; }
                double rel = (double)P[idx[1]] / W; if (k > 1 && rel < minrel) minrel = rel;
                for (int i = 2; i < k; i++) if (P[idx[i]] - P[idx[i-1]] < minsep) { minsep = P[idx[i]] - P[idx[i-1]]; msn = n; }
            }
            int alive = 0, ok = 0; for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M' && P[i] == W - 2) ok = 1; }
            if (alive == 2 && ok) break; }
    }
    printf("rounds with a right-end meeting (after round 1): smallest first-mark position %lld (n = %lld), smallest relative %.3g; smallest neighbour separation %lld (n = %lld); most marks %d\n", minpos, mpn, minrel, minsep, msn, maxm);
}
