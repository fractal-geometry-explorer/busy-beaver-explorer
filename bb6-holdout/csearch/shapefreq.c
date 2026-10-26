#include "model_core_r.h"
#include <string.h>
/* Frequency of every round shape over many cycles (rounds with or without meetings). */
#define NS 4000
static char sname[NS][16]; static long long scnt[NS]; static int nsh;
int main(int argc, char **argv) {
    long N = atol(argv[1]); ll start = atoll(argv[2]); unsigned long long s = 0x77777777ULL;
    for (long t = 0; t < N; t++) {
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll n = start + (ll)(s % (unsigned long long)start);
        nm = 0; halted = 0; bad = 0; nend = 0; W = 2 * n + 6; add('G', 1); add('M', W - 2);
        for (int r = 1; r <= 5000; r++) { CUR_RD = r; do_round(); if (halted || bad) break;
            int idx[MAXM], k = 0; for (int i = 0; i < nm; i++) if (A[i]) idx[k++] = i;
            for (int i = 1; i < k; i++) { int v = idx[i], j = i - 1; while (j >= 0 && P[idx[j]] > P[v]) { idx[j+1] = idx[j]; j--; } idx[j+1] = v; }
            char sh[16] = {0}; for (int i = 0; i < k && i < 15; i++) sh[i] = T[idx[i]];
            int f = -1; for (int u = 0; u < nsh; u++) if (!strcmp(sname[u], sh)) { f = u; break; }
            if (f < 0 && nsh < NS) { f = nsh++; strcpy(sname[f], sh); } if (f >= 0) scnt[f]++;
            int alive = 0, ok = 0; for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M' && P[i] == W - 2) ok = 1; }
            if (alive == 2 && ok) break; }
    }
    printf("%d shapes\n", nsh); for (int u = 0; u < nsh; u++) printf("%s %lld\n", sname[u], scnt[u]);
}
