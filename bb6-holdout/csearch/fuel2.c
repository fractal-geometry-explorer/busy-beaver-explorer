#include "model_core_r.h"
#include <string.h>
/* Check: from a cycle-start state (G, W a, W b, W c, end E), the number of complete 8-round cycles that follow
   equals min(floor((fL - 3)/6), floor((fR - 1)/4)) with fL = v2(1029 b - 784 E - 1302), fR = v2(E - c - 1)? */
static int v2(ll x) { if (!x) return 63; int c = 0; while (!(x & 1)) { x >>= 1; c++; } return c; }
static const char *CYC[8] = {"GBW", "GMB", "GMWW", "GMB", "GMWW", "GWWW", "GBW", "GWWW"};
static char hist[6000][16];
int main(int argc, char **argv) {
    long N = atol(argv[1]); int mode = atoi(argv[2]); ll start = argc > 3 ? atoll(argv[3]) : 0;
    unsigned long long s = 0x9E3779B97F4A7C15ULL; static long long agree[3]; static long long tab[8][8];
    ll fls[6000], frs[6000];
    for (long t = 0; t < N; t++) {
        ll n;
        if (mode == 2) { if (scanf("%lld", &n) != 1) break; } else { s ^= s << 13; s ^= s >> 7; s ^= s << 17; n = start + (ll)(s >> 20); }
        nm = 0; halted = 0; bad = 0; nend = 0; W = 2 * n + 6; add('G', 1); add('M', W - 2);
        int nr = 0;
        for (int r = 1; r <= 5000; r++) {
            CUR_RD = r; do_round(); if (halted || bad) break;
            int idx[MAXM], k = 0; for (int i = 0; i < nm; i++) if (A[i]) idx[k++] = i;
            for (int i = 1; i < k; i++) { int v = idx[i], j = i - 1; while (j >= 0 && P[idx[j]] > P[v]) { idx[j+1] = idx[j]; j--; } idx[j+1] = v; }
            char *sh = hist[nr]; memset(sh, 0, 16); for (int i = 0; i < k && i < 15; i++) sh[i] = T[idx[i]];
            fls[nr] = -1;
            if (!strcmp(sh, "GWWW")) { ll b = P[idx[2]], c = P[idx[3]]; fls[nr] = v2(1029 * b - 784 * W - 1302); frs[nr] = v2(W - c - 1); }
            nr++;
            int alive = 0, ok = 0; for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M' && P[i] == W - 2) ok = 1; }
            if (alive == 2 && ok) break;
        }
        for (int i = 0; i + 2 < nr; i++) {
            if (fls[i] < 0 || strcmp(hist[i+1], "GBW") || strcmp(hist[i+2], "GMB")) continue;
            int m = 0; while (1) { int okc = 1; for (int j = 0; j < 8; j++) { int q = i + 1 + 8 * m + j; if (q >= nr || strcmp(hist[q], CYC[j])) { okc = 0; break; } } if (!okc) break; m++; }
            int pl = fls[i] >= 3 ? (fls[i] - 3) / 6 : -1, pr = (frs[i] - 1) / 4; int pred = pl < pr ? pl : pr; if (pred < 0) pred = 0;
            agree[m == pred ? 0 : (m > pred ? 1 : 2)]++;
            if (m < 8 && pred < 8) tab[pred][m]++;
        }
    }
    printf("cycle starts: predicted = actual %lld, actual more %lld, actual fewer %lld\n", agree[0], agree[1], agree[2]);
    for (int a = 0; a < 4; a++) { printf(" predicted %d:", a); for (int b = 0; b < 4; b++) printf(" %8lld", tab[a][b]); printf("\n"); }
}
