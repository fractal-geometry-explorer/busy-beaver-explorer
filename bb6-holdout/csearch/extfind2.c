#include "model_core_r.h"
#include <string.h>
/* Random G, M m, B r states near a given geometry (random low digits): print those that later run a full pass of the
   loop with an extra wall. */
static const char *EXT[8] = {"GWWWW", "GBWW", "GMBW", "GMWWW", "GMBW", "GMWWW", "GWWWW", "GBWW"};
int main(int argc, char **argv) {
    long N = atol(argv[1]); unsigned long long s = 0xFEEDFACECAFEULL; int found = 0;
    ll E0 = 3358942591030LL, m0 = 341552634072LL, r0 = 2782444387539LL;
    for (long t = 0; t < N && found < 5; t++) {
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll E = (E0 + (ll)(s >> 34)) & ~1LL;
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll m = (m0 + (ll)(s >> 34)) & ~1LL;
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll r = (r0 + (ll)(s >> 34)) | 1;
        nm = 0; halted = 0; bad = 0; nend = 0; W = E; add('G', 1); add('M', m); add('B', r);
        char h[40][16]; int nr = 0;
        for (int rd = 0; rd < 30; rd++) { CUR_RD = rd + 1; do_round(); if (halted || bad) break;
            int idx[MAXM], q = 0; for (int i = 0; i < nm; i++) if (A[i]) idx[q++] = i;
            for (int i = 1; i < q; i++) { int v = idx[i], j = i - 1; while (j >= 0 && P[idx[j]] > P[v]) { idx[j+1] = idx[j]; j--; } idx[j+1] = v; }
            memset(h[nr], 0, 16); for (int i = 0; i < q && i < 15; i++) h[nr][i] = T[idx[i]]; nr++;
            int alive = 0, ok = 0; for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M' && P[i] == W - 2) ok = 1; }
            if (alive == 2 && ok) break; }
        for (int i = 0; i + 8 <= nr; i++) { int okk = 1; for (int k = 0; k < 8; k++) if (strcmp(h[i + k], EXT[k])) { okk = 0; break; }
            if (okk) { printf("%lld %lld %lld at round %d:", E, m, r, i + 1); for (int k = 0; k < nr; k++) printf(" %s", h[k]); printf("\n"); found++; break; } }
    }
    printf("found %d\n", found);
}
