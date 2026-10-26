#include "model_core_r.h"
#include <string.h>
/* For each n (stdin), print the shape sequence of its longest right-end run, from the round of its first meeting to the
   round of its last meeting, with the round offset of each meeting. */
static ll pred(ll d) { return (d % 4 == 2) ? (d - 2) / 2 : d / 2 + 4; }
static char shapes[6000][16]; static int nrd;
int main(void) {
    ll n;
    while (scanf("%lld", &n) == 1) {
        nm = 0; halted = 0; bad = 0; nend = 0; W = 2 * n + 6; add('G', 1); add('M', W - 2); nrd = 0;
        for (int r = 1; r <= 5000; r++) {
            CUR_RD = r; do_round(); if (halted || bad) break;
            int idx[MAXM], k = 0; for (int i = 0; i < nm; i++) if (A[i]) idx[k++] = i;
            for (int i = 1; i < k; i++) { int v = idx[i], j = i - 1; while (j >= 0 && P[idx[j]] > P[v]) { idx[j+1] = idx[j]; j--; } idx[j+1] = v; }
            char *sh = shapes[nrd++]; memset(sh, 0, 16); for (int i = 0; i < k && i < 15; i++) sh[i] = T[idx[i]];
            int alive = 0, ok = 0; for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M' && P[i] == W - 2) ok = 1; }
            if (alive == 2 && ok) break;
        }
        int best = 1, bs = 0, cur = 1, cs = 0;
        for (int i = 1; i < nend; i++) { if (endd[i] == pred(endd[i-1])) { cur++; if (cur > best) { best = cur; bs = cs; } } else { cur = 1; cs = i; } }
        int r0 = endrd[bs], r1 = endrd[bs + best - 1];
        printf("%lld chain %d rounds %d-%d:", n, best, r0, r1);
        int e = bs;
        for (int r = r0; r <= r1; r++) { int c = 0; while (e < nend && endrd[e] == r && e < bs + best) { c++; e++; } printf(" %s%s", shapes[r-1], c == 0 ? "" : c == 1 ? "*" : "**"); }
        printf("\n");
    }
}
