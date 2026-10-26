#include "model_core_r.h"
#include <string.h>
int main(int argc, char **argv) {
    long N = atol(argv[1]); ll start = atoll(argv[2]); const char *want = argv[3]; unsigned long long s = 0x77777777ULL; int found = 0;
    for (long t = 0; t < N && found < 5; t++) {
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll n = start + (ll)(s % (unsigned long long)start);
        nm = 0; halted = 0; bad = 0; nend = 0; W = 2 * n + 6; add('G', 1); add('M', W - 2);
        for (int r = 1; r <= 5000; r++) { CUR_RD = r; do_round(); if (halted || bad) break;
            int idx[MAXM], k = 0; for (int i = 0; i < nm; i++) if (A[i]) idx[k++] = i;
            for (int i = 1; i < k; i++) { int v = idx[i], j = i - 1; while (j >= 0 && P[idx[j]] > P[v]) { idx[j+1] = idx[j]; j--; } idx[j+1] = v; }
            char sh[16] = {0}; for (int i = 0; i < k && i < 15; i++) sh[i] = T[idx[i]];
            if (!strcmp(sh, want)) { printf("%lld round %d\n", n, r); found++; break; }
            int alive = 0, ok = 0; for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M' && P[i] == W - 2) ok = 1; }
            if (alive == 2 && ok) break; }
    }
}
