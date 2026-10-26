#include "model_core_r.h"
#include <string.h>
/* Random states G, W a, W b, W c, W d, end E: print those whose next 8 rounds follow the loop with an extra wall,
   and count how many passes of it follow. */
static const char *EXT[8] = {"GWWWW", "GBWW", "GMBW", "GMWWW", "GMBW", "GMWWW", "GWWWW", "GBWW"};
int main(int argc, char **argv) {
    long N = atol(argv[1]); unsigned long long s = 0xDEADBEEF12345ULL; int found = 0; long long hist[20] = {0};
    for (long t = 0; t < N && found < 20; t++) {
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll E = (ll)((s >> 24) | (1ULL << 40)) & ~3LL;
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll a = (ll)(E * (0.05 + 0.3 * ((s >> 11) / 9007199254740992.0)));
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll b = (ll)(E * (0.4 + 0.5 * ((s >> 11) / 9007199254740992.0)));
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; double f1 = (s >> 11) / 9007199254740992.0;
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; double f2 = (s >> 11) / 9007199254740992.0;
        ll c = E - (ll)(E * 0.3 * f1 * f1) - 10, d = E - (ll)((E - c) * f2) - 3;
        a |= 1; b &= ~1LL; c |= 1; if (d <= c + 4) continue; if (!(a < b && b < c && c < d && d < E - 2)) continue;
        for (int pd = 0; pd < 2; pd++) {
            ll dd = (d & ~1LL) | pd;
            nm = 0; halted = 0; bad = 0; nend = 0; W = E; add('G', 1); add('W', a); add('W', b); add('W', c); add('W', dd);
            int ph0 = -1, k = 0;
            for (int r = 0; r < 64; r++) { CUR_RD = r + 1; do_round(); if (halted || bad) break;
                int idx[MAXM], q = 0; for (int i = 0; i < nm; i++) if (A[i]) idx[q++] = i;
                for (int i = 1; i < q; i++) { int v = idx[i], j = i - 1; while (j >= 0 && P[idx[j]] > P[v]) { idx[j+1] = idx[j]; j--; } idx[j+1] = v; }
                char sh[16] = {0}; for (int i = 0; i < q && i < 15; i++) sh[i] = T[idx[i]];
                if (r == 0) { if (!strcmp(sh, "GBWW")) ph0 = 0; else break; }
                /* phases: from GWWWW at 0 or 6; accept either continuation */
                int okk = 0; for (int ph = 0; ph < 8; ph += 6) if (!strcmp(sh, EXT[(ph + r + 1) % 8])) okk = 1;
                if (!okk) break; k = r + 1;
            }
            if (k >= 8) { hist[k / 8 < 19 ? k / 8 : 19]++; if (found < 6) printf("%lld %lld %lld %lld %lld  rounds following the extended loop: %d\n", E, a, b, c, dd, k); found++; }
        }
    }
    printf("found %d\n", found);
}
