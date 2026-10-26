#include "model_core_r.h"
#include <string.h>
/* Shape of the state at the start of the round in which each right-end run has its first meeting, with counts, the
   longest run from that shape, and the most meetings it makes before entering the loop (or in total, if never). */
static ll pred(ll d) { return (d % 4 == 2) ? (d - 2) / 2 : d / 2 + 4; }
static const char *LOOP[8] = {"GWWW", "GBW", "GMB", "GMWW", "GMB", "GMWW", "GWWW", "GBW"};
static char hist[6000][16];
#define NS 2000
static char sname[NS][16]; static long long scnt[NS]; static int smaxL[NS], smaxpre[NS]; static int nsh;
int main(int argc, char **argv) {
    long N = atol(argv[1]); ll start = atoll(argv[2]); unsigned long long s = 0x9E3779B97F4A7C15ULL ^ (unsigned long long)start;
    for (long t = 0; t < N; t++) {
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll n = start + (ll)(s % (unsigned long long)start);
        nm = 0; halted = 0; bad = 0; nend = 0; W = 2 * n + 6; add('G', 1); add('M', W - 2); int nr = 0;
        strcpy(hist[0], "GM(clean)");
        for (int r = 1; r <= 5000; r++) { CUR_RD = r; do_round(); if (halted || bad) break;
            int idx[MAXM], k = 0; for (int i = 0; i < nm; i++) if (A[i]) idx[k++] = i;
            for (int i = 1; i < k; i++) { int v = idx[i], j = i - 1; while (j >= 0 && P[idx[j]] > P[v]) { idx[j+1] = idx[j]; j--; } idx[j+1] = v; }
            nr++; memset(hist[nr], 0, 16); for (int i = 0; i < k && i < 15; i++) hist[nr][i] = T[idx[i]];
            int alive = 0, ok = 0; for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M' && P[i] == W - 2) ok = 1; }
            if (alive == 2 && ok) break; }
        int i = 0;
        while (i < nend) {
            int j = i + 1; while (j < nend && endd[j] == pred(endd[j-1])) j++;
            int L = j - i, r0 = endrd[i];
            /* hist[r] = shape after round r; state at the start of round r0 is hist[r0-1] */
            const char *sh = hist[r0 - 1];
            /* meetings before the first loop stretch of >= 4 rounds starting at or after r0 */
            int pre = L, q;
            for (q = r0; q <= endrd[j-1]; q++) { int bk = 0;
                for (int ph = 0; ph < 8; ph++) { int k = 0; while (q + k <= nr && !strcmp(hist[q + k], LOOP[(ph + k) % 8])) k++; if (k > bk) bk = k; }
                if (bk >= 4) { pre = 0; for (int e = i; e < j; e++) if (endrd[e] < q) pre++; break; } }
            int f = -1; for (int u = 0; u < nsh; u++) if (!strcmp(sname[u], sh)) { f = u; break; }
            if (f < 0 && nsh < NS) { f = nsh++; strcpy(sname[f], sh); }
            if (f >= 0) { scnt[f]++; if (L > smaxL[f]) smaxL[f] = L; if (pre > smaxpre[f]) smaxpre[f] = pre; }
            i = j;
        }
    }
    printf("%d shapes at run starts\n", nsh);
    for (int u = 0; u < nsh; u++) printf("  %-12s %12lld  longest run %2d  most meetings before the loop %d\n", sname[u], scnt[u], smaxL[u], smaxpre[u]);
}
