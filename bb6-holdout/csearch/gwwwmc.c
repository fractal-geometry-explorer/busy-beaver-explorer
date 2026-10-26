#include "model_core_r.h"
#include <string.h>
/* random integer loop states (a odd, b even, c odd, E even) at a fixed geometry: tally the first rounds' shapes */
#define NS 400
static char nm_[NS][64]; static long long cnt[NS]; static int ns;
int main(int argc, char **argv) {
    long N = atol(argv[1]); int depth = atoi(argv[2]); unsigned long long s = 0x1234ABCDULL;
    double ga = 1559396385.0 / 10395969088.0, gb = 6743276446.0 / 10395969088.0, gc = 10381864607.0 / 10395969088.0;
    for (long t = 0; t < N; t++) {
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll E = ((ll)(s >> 20) | (1LL << 43)) & ~1LL;
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll a = ((ll)(E * ga) + (ll)(s >> 40)) | 1;
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll b = ((ll)(E * gb) + (ll)(s >> 40)) & ~1LL;
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll c = ((ll)(E * gc) + (ll)(s >> 40)) | 1;
        nm = 0; halted = 0; bad = 0; nend = 0; W = E; add('W', a); add('W', b); add('W', c); add('G', 1);
        char key[64] = "";
        for (int r = 0; r < depth; r++) { CUR_RD = r + 1; do_round(); if (halted || bad) { strcat(key, " X"); break; }
            int idx[MAXM], q = 0; for (int i = 0; i < nm; i++) if (A[i]) idx[q++] = i;
            for (int i = 1; i < q; i++) { int v = idx[i], j = i - 1; while (j >= 0 && P[idx[j]] > P[v]) { idx[j+1] = idx[j]; j--; } idx[j+1] = v; }
            char sh[16] = {0}; for (int i = 0; i < q && i < 15; i++) sh[i] = T[idx[i]];
            strcat(key, " "); strcat(key, sh); }
        int f = -1; for (int i = 0; i < ns; i++) if (!strcmp(nm_[i], key)) f = i;
        if (f < 0 && ns < NS) { f = ns++; strcpy(nm_[f], key); } if (f >= 0) cnt[f]++;
    }
    for (int i = 0; i < ns; i++) printf("%10lld %s\n", cnt[i], nm_[i]);
}
