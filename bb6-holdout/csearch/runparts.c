#include "model_core_r.h"
#include <string.h>
/* For every right-end run in every sampled cycle: meetings inside its longest stretch of loop rounds, and meetings
   outside it (before + after).  Reports the largest non-loop count, loop re-entries, and examples. */
static ll pred(ll d) { return (d % 4 == 2) ? (d - 2) / 2 : d / 2 + 4; }
static const char *LOOP[8] = {"GWWW", "GBW", "GMB", "GMWW", "GMB", "GMWW", "GWWW", "GBW"};
static char hist[6000][16];
int main(int argc, char **argv) {
    long N = atol(argv[1]); ll start = atoll(argv[2]); int mode = atoi(argv[3]);
    unsigned long long s = 0x2545F4914F6CDD1DULL ^ (unsigned long long)start;
    static long long tab[16][40]; long long runs = 0, reentry = 0; int maxnon = 0;
    for (long t = 0; t < N; t++) {
        ll n; if (mode == 2) { if (scanf("%lld", &n) != 1) break; } else { s ^= s << 13; s ^= s >> 7; s ^= s << 17; n = start + (ll)(s % (unsigned long long)start); }
        nm = 0; halted = 0; bad = 0; nend = 0; W = 2 * n + 6; add('G', 1); add('M', W - 2); int nr = 0;
        for (int r = 1; r <= 5000; r++) { CUR_RD = r; do_round(); if (halted || bad) break;
            int idx[MAXM], k = 0; for (int i = 0; i < nm; i++) if (A[i]) idx[k++] = i;
            for (int i = 1; i < k; i++) { int v = idx[i], j = i - 1; while (j >= 0 && P[idx[j]] > P[v]) { idx[j+1] = idx[j]; j--; } idx[j+1] = v; }
            memset(hist[nr], 0, 16); for (int i = 0; i < k && i < 15; i++) hist[nr][i] = T[idx[i]]; nr++;
            int alive = 0, ok = 0; for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M' && P[i] == W - 2) ok = 1; }
            if (alive == 2 && ok) break; }
        int i = 0;
        while (i < nend) {
            int j = i + 1; while (j < nend && endd[j] == pred(endd[j-1])) j++;
            int L = j - i, r0 = endrd[i], r1 = endrd[j-1];
            /* loop stretches within rounds r0..r1 (1-based rounds; hist index r-1) */
            int nst = 0, bestm = 0; int q = r0;
            while (q <= r1) {
                int bk = 0;
                for (int ph = 0; ph < 8; ph++) { int k = 0; while (q + k <= r1 && !strcmp(hist[q - 1 + k], LOOP[(ph + k) % 8])) k++; if (k > bk) bk = k; }
                if (bk >= 4) { int m = 0; for (int e = i; e < j; e++) if (endrd[e] >= q && endrd[e] < q + bk) m++; nst++; if (m > bestm) bestm = m; q += bk; } else q++;
            }
            int non = L - bestm; if (non > maxnon) { maxnon = non; printf("  new largest non-loop count %d: n = %lld, run of %d meetings, %d in the loop\n", non, n, L, bestm); fflush(stdout); }
            if (nst >= 2) { reentry++; if (reentry <= 5) printf("  loop entered twice in one run: n = %lld, run of %d\n", n, L); }
            int a = bestm > 39 ? 39 : bestm, b = non > 15 ? 15 : non; tab[b][a]++; runs++;
            i = j;
        }
    }
    printf("%lld runs, %lld with two loop stretches; largest non-loop count %d\n", runs, reentry, maxnon);
    printf("rows: meetings outside the loop; columns: meetings in the loop 0..16\n");
    for (int b = 0; b < 16; b++) { long long rs = 0; for (int a = 0; a < 40; a++) rs += tab[b][a]; if (!rs) continue;
        printf("%3d:", b); for (int a = 0; a <= 16; a++) printf(" %9lld", tab[b][a]); printf("\n"); }
}
