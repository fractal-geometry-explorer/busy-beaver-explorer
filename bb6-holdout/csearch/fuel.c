#include "model_core_r.h"
#include <string.h>
/* At every cycle-start state (G, W a, W b, W c, end E, followed by G-B-W then G-M-B) record
   fL = v2(1029 b - 784 E - 1302)  (left fuel: the cycle's left condition is b = 16E/21 + 62/49 2-adically)
   fR = v2(E - c - 1)             (right fuel: the end countdown)                                          */
static int v2(ll x) { if (!x) return 63; int c = 0; while (!(x & 1)) { x >>= 1; c++; } return c; }
int main(int argc, char **argv) {
    long N = atol(argv[1]); ll start = atoll(argv[2]); int mode = argc > 3 ? atoi(argv[3]) : 0;
    static long long tab[64][64]; long long ncs = 0; unsigned long long s = 0x9E3779B97F4A7C15ULL;
    for (long t = 0; t < N; t++) {
        ll n;
        if (mode == 2) { if (scanf("%lld", &n) != 1) break; } else if (mode == 0) n = start + t;
        else { s ^= s << 13; s ^= s >> 7; s ^= s << 17; n = start + (ll)(s >> 20); }
        nm = 0; halted = 0; bad = 0; nend = 0; W = 2 * n + 6; add('G', 1); add('M', W - 2);
        char sh[3][16]; ll pa = 0, pb = 0, pc = 0, pE = 0; int have = 0;
        memset(sh, 0, sizeof sh);
        for (int r = 1; r <= 5000; r++) {
            CUR_RD = r; do_round(); if (halted || bad) break;
            int idx[MAXM], k = 0; for (int i = 0; i < nm; i++) if (A[i]) idx[k++] = i;
            for (int i = 1; i < k; i++) { int v = idx[i], j = i - 1; while (j >= 0 && P[idx[j]] > P[v]) { idx[j+1] = idx[j]; j--; } idx[j+1] = v; }
            memmove(sh[0], sh[1], 32); memset(sh[2], 0, 16); for (int i = 0; i < k && i < 15; i++) sh[2][i] = T[idx[i]];
            if (have == 2 && !strcmp(sh[1], "GBW") && !strcmp(sh[2], "GMB")) {
                int fl = v2(1029 * pb - 784 * pE - 1302), fr = v2(pE - pc - 1); if (fl > 63) fl = 63; tab[fl][fr]++; ncs++;
                if (fl >= 14 || fr >= 9) printf("  n = %lld: cycle start with left fuel %d, right fuel %d\n", n, fl, fr);
            }
            if (have) have++;
            if (!strcmp(sh[2], "GWWW")) { pa = P[idx[1]]; pb = P[idx[2]]; pc = P[idx[3]]; pE = W; have = 1; }
            int alive = 0, ok = 0; for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M' && P[i] == W - 2) ok = 1; }
            if (alive == 2 && ok) break;
        }
    }
    printf("%lld cycle starts. rows: left fuel; columns: right fuel 0..12\n", ncs);
    for (int a = 0; a < 25; a++) { long long rs = 0; for (int b = 0; b < 64; b++) rs += tab[a][b]; if (!rs) continue; printf("L%2d:", a); for (int b = 0; b <= 12; b++) printf(" %8lld", tab[a][b]); printf("\n"); }
}
