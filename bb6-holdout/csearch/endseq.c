#include "model_core_r.h"
/* For each n: the right-end meeting distances across the whole cycle, as halvings log2(W/d), with run breaks marked. */
static ll pred(ll d) { return (d % 4 == 2) ? (d - 2) / 2 : d / 2 + 4; }
int main(void) {
    ll n;
    while (scanf("%lld", &n) == 1) {
        nm = 0; halted = 0; bad = 0; nend = 0; W = 2 * n + 6; add('G', 1); add('M', W - 2);
        ll W0 = W; int r;
        for (r = 1; r <= 5000; r++) { CUR_RD = r; do_round(); if (halted || bad) break;
            int alive = 0, ok = 0; for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M' && P[i] == W - 2) ok = 1; }
            if (alive == 2 && ok) break; }
        printf("%lld:", n);
        for (int i = 0; i < nend; i++) { int br = (i > 0 && endd[i] != pred(endd[i-1])); printf("%s%.1f", br ? " | " : " ", log2((double)W0 / (endd[i] + 2))); }
        printf("\n");
    }
}
