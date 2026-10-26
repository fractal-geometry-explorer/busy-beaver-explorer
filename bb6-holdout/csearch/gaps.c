#include "model_core_r.h"
#include <string.h>
/* For n whose cycle reaches a loop pass start (G,W a,W b,W c,end E then G-B-W, G-M-B), compute the line gaps:
   with n_j = n + 2^K j (j = 1, 2) following the same path, R = E - c - 1 and L = 1029b + 1960E - 2744c - 4046 are
   affine in j: Delta = lamR*L1 - lamL*R1;  GL = v(Delta) - v(lamR),  GR = v(Delta) - v(lamL).
   Passes from that start are at most max((GL-1)/6, (GR-1)/4). */
typedef __int128 i128;
static int v2q(i128 x) { if (!x) return 999; int c = 0; while (!(x & 1)) { x >>= 1; c++; } return c; }
#define MAXR 3000
static char hist[MAXR][16]; static i128 RR[MAXR], LL[MAXR]; static int isg[MAXR];
static int runone(ll n, char h[][16], i128 *Rv, i128 *Lv, int *g) {
    nm = 0; halted = 0; bad = 0; nend = 0; W = 2 * n + 6; add('G', 1); add('M', W - 2); int nr = 0;
    for (int r = 1; r < MAXR; r++) {
        CUR_RD = r; do_round(); if (halted || bad) return -1;
        int idx[MAXM], k = 0; for (int i = 0; i < nm; i++) if (A[i]) idx[k++] = i;
        for (int i = 1; i < k; i++) { int v = idx[i], j = i - 1; while (j >= 0 && P[idx[j]] > P[v]) { idx[j+1] = idx[j]; j--; } idx[j+1] = v; }
        memset(h[nr], 0, 16); for (int i = 0; i < k && i < 15; i++) h[nr][i] = T[idx[i]];
        g[nr] = 0;
        if (!strcmp(h[nr], "GWWW")) { ll b = P[idx[2]], c = P[idx[3]]; Rv[nr] = (i128)W - c - 1; Lv[nr] = (i128)1029 * b + (i128)1960 * W - (i128)2744 * c - 4046; g[nr] = 1; }
        nr++;
        int alive = 0, ok = 0; for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M' && P[i] == W - 2) ok = 1; }
        if (alive == 2 && ok) break;
    }
    return nr;
}
static char h1[MAXR][16], h2[MAXR][16]; static i128 R1[MAXR], L1[MAXR], R2[MAXR], L2[MAXR]; static int g1[MAXR], g2[MAXR];
int main(int argc, char **argv) {
    long N = atol(argv[1]); ll start = atoll(argv[2]); int mode = atoi(argv[3]); int K = 50;
    static long long tab[40][40]; long long nent = 0, skipped = 0; unsigned long long s = 0xABCDEF12345ULL;
    for (long t = 0; t < N; t++) {
        ll n;
        if (mode == 2) { if (scanf("%lld", &n) != 1) break; } else { s ^= s << 13; s ^= s >> 7; s ^= s << 17; n = start + (ll)(s % (unsigned long long)start); }
        int nr = runone(n, hist, RR, LL, isg); if (nr < 0) continue;
        int any = 0; for (int i = 0; i + 2 < nr; i++) if (isg[i] && !strcmp(hist[i+1], "GBW") && !strcmp(hist[i+2], "GMB")) { any = 1; break; }
        if (!any) continue;
        ll nb = n & ((1LL << K) - 1);
        int a1 = runone(nb + (1LL << K), h1, R1, L1, g1), a2 = runone(nb + (2LL << K), h2, R2, L2, g2);
        if (a1 != a2 || a1 < 0) { skipped++; continue; }
        int same = 1; for (int i = 0; i < a1; i++) if (strcmp(h1[i], h2[i])) { same = 0; break; }
        if (!same) { skipped++; continue; }
        for (int i = 0; i + 2 < a1; i++) {
            if (!(g1[i] && !strcmp(h1[i+1], "GBW") && !strcmp(h1[i+2], "GMB"))) continue;
            i128 lR = R2[i] - R1[i], lL = L2[i] - L1[i]; i128 D = lR * L1[i] - lL * R1[i];
            int GL = v2q(D) - v2q(lR), GR = v2q(D) - v2q(lL);
            if (GL < 0) GL = 0; if (GR < 0) GR = 0; if (GL > 39) GL = 39; if (GR > 39) GR = 39;
            tab[GL][GR]++; nent++;
            if (GR >= 10 || GL >= 14) printf("  n = %lld round %d: GL %d GR %d\n", n, i + 1, GL, GR);
        }
    }
    printf("%lld pass starts (%lld n skipped: path differs between j = 1, 2)\nGL\\GR:", nent, skipped);
    for (int b = 0; b <= 14; b++) printf(" %6d", b); printf("\n");
    for (int a = 0; a < 40; a++) { long long rs = 0; for (int b = 0; b < 40; b++) rs += tab[a][b]; if (!rs) continue; printf("%5d:", a); for (int b = 0; b <= 14; b++) printf(" %6lld", tab[a][b]); printf("\n"); }
}
