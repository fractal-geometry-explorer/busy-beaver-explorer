#include "model_core_r.h"
#include <string.h>
/* One example state (positions and end) for each shape found at the start of a run's first-meeting round. Also the
   largest number of marks on the tape at any round. */
static ll pred(ll d) { return (d % 4 == 2) ? (d - 2) / 2 : d / 2 + 4; }
#define NS 200
static char sname[NS][16]; static int nsh; static int maxmarks = 0;
static char shp[6000][16]; static ll pos[6000][16]; static ll Ws[6000]; static int npos[6000];
int main(int argc, char **argv) {
    long N = atol(argv[1]); ll start = atoll(argv[2]); unsigned long long s = 0x1F2E3D4C5B6A7988ULL;
    for (long t = 0; t < N; t++) {
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll n = start + (ll)(s % (unsigned long long)start);
        nm = 0; halted = 0; bad = 0; nend = 0; W = 2 * n + 6; add('G', 1); add('M', W - 2); int nr = 0;
        for (int r = 1; r <= 5000; r++) { CUR_RD = r; do_round(); if (halted || bad) break;
            int idx[MAXM], k = 0; for (int i = 0; i < nm; i++) if (A[i]) idx[k++] = i;
            if (k > maxmarks) { maxmarks = k; }
            for (int i = 1; i < k; i++) { int v = idx[i], j = i - 1; while (j >= 0 && P[idx[j]] > P[v]) { idx[j+1] = idx[j]; j--; } idx[j+1] = v; }
            nr++; memset(shp[nr], 0, 16); npos[nr] = k < 15 ? k : 15; for (int i = 0; i < npos[nr]; i++) { shp[nr][i] = T[idx[i]]; pos[nr][i] = P[idx[i]]; } Ws[nr] = W;
            int alive = 0, ok = 0; for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M' && P[i] == W - 2) ok = 1; }
            if (alive == 2 && ok) break; }
        for (int i = 0; i < nend; i++) {
            if (i > 0 && endd[i] == pred(endd[i-1])) continue;
            int r0 = endrd[i]; if (r0 < 2) continue; int q = r0 - 1;
            int f = -1; for (int u = 0; u < nsh; u++) if (!strcmp(sname[u], shp[q])) { f = u; break; }
            if (f < 0 && nsh < NS) { f = nsh++; strcpy(sname[f], shp[q]); printf("%s %lld", shp[q], Ws[q]); for (int k = 1; k < npos[q]; k++) printf(" %lld", pos[q][k]); printf("\n"); }
        }
    }
    fprintf(stderr, "largest number of marks at any round: %d\n", maxmarks);
}
