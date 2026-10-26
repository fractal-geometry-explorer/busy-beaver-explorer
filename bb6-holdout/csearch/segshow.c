#include <string.h>
/* Mark model of 1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE (same rules as tracecycle.py), for fast sweeps.
   For each n: next clean n, rounds, and the meetings between a gap and the end marker (the right-end cascade). */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef long long ll;
#define MAXM 128
static char T[MAXM]; static ll P[MAXM]; static int A[MAXM]; static int nm;
static ll W;
static int halted, bad;
static ll endd[4096]; static int nend; static int outs[4096]; static int nout;
static int add(char t, ll p) { for (int i = 0; i < nm; i++) if (!A[i]) { T[i] = t; P[i] = p; A[i] = 1; return i; }
    if (nm >= MAXM) { bad = 1; return 0; } T[nm] = t; P[nm] = p; A[nm] = 1; return nm++; }
static int first_right(ll x) { int b = -1; for (int i = 0; i < nm; i++) if (A[i] && P[i] > x && (b < 0 || P[i] < P[b])) b = i; return b; }
static int last_mark(void) { int b = -1; for (int i = 0; i < nm; i++) if (A[i] && (b < 0 || P[i] > P[b])) b = i; return b; }
static int packet_back(ll x) {
    int b = -1; for (int i = 0; i < nm; i++) if (A[i] && P[i] < x && T[i] != 'M' && (b < 0 || P[i] > P[b])) b = i;
    if (b < 0) return -1;
    if (T[b] == 'B') { halted = 1; return -1; }
    if (T[b] == 'G') { P[b] += 2; return b; }
    ll q = P[b]; T[b] = 'M'; P[b] = q - 1; return add('G', q + 1);
}
static int shift_from(ll x) {
    int k = first_right(x);
    if (k < 0) { W += 2; add('M', W - 2); return packet_back(W - 2); }
    if (T[k] == 'M') { T[k] = 'G'; return k; }
    if (T[k] == 'W') { T[k] = 'B'; return packet_back(P[k]); }
    if (T[k] == 'B') { T[k] = 'W'; P[k] += 2; return packet_back(P[k]); }
    bad = 2; return -1;
}
static void do_round(void) {
    int gap = -1; for (int i = 0; i < nm; i++) if (A[i] && T[i] == 'G' && P[i] == 1) gap = i;
    while (gap >= 0 && !halted && !bad) {
        ll g = P[gap]; int m = first_right(g);
        if (m < 0) { A[gap] = 0; W += 3; add('M', W - 2); gap = packet_back(W - 2); continue; }
        if (T[m] == 'M') {
            ll d = P[m] - g - 3;
            if (d < 0 || (d & 1)) { bad = 3; return; }
            if (m == last_mark() && nend < 4096) endd[nend++] = d; if (nout < 4096) outs[nout++] = (int)(d % 4);
            if (d % 4 == 0) { P[m] = g + d / 2 - 1; P[gap] = g + d / 2 + 1; }
            else { A[gap] = 0; T[m] = 'W'; P[m] = g + d / 2 + 3; gap = packet_back(P[m]); }
        } else if (T[m] == 'W') { ll x = P[m]; A[gap] = 0; A[m] = 0; gap = shift_from(x); }
        else if (T[m] == 'B') { T[m] = 'W'; P[m] -= 1; gap = shift_from(P[m]); }
        else { bad = 4; return; }
    }
    ll extra = 2;
    for (int i = 0; i < nm; i++) if (A[i] && T[i] == 'M' && P[i] == 0) { T[i] = 'W'; P[i] = 1; extra = 4; }
    for (int i = 0; i < nm; i++) if (A[i]) P[i] += extra;
    W += extra; add('G', 1);
}


static unsigned long long s[2];
static unsigned long long rnd(void) { unsigned long long s1 = s[0]; const unsigned long long s0 = s[1]; s[0] = s0;
    s1 ^= s1 << 23; s[1] = s1 ^ s0 ^ (s1 >> 17) ^ (s0 >> 26); return s[1] + s0; }
static void shape(char *out) { int idx[MAXM], k = 0; for (int i = 0; i < nm; i++) if (A[i]) idx[k++] = i;
    for (int i = 1; i < k; i++) { int v = idx[i], j = i - 1; while (j >= 0 && P[idx[j]] > P[v]) { idx[j+1] = idx[j]; j--; } idx[j+1] = v; }
    for (int i = 0; i < k; i++) out[i] = T[idx[i]]; out[k] = 0; }
static const char *PSH[8] = {"GBWW", "GWWWW", "GBWW", "GMBW", "GMWWW", "GMBW", "GMWWW", "GWWWW"};
static const char *CYC[8] = {"GBW", "GMB", "GMWW", "GMB", "GMWW", "GWWW", "GBW", "GWWW"};


int main(int argc, char **argv) {
    for (int a = 1; a < argc; a++) {
        ll n = atoll(argv[a]);
        nm = 0; halted = 0; bad = 0; nend = 0; nout = 0; W = 2 * n + 6; add('G', 1); add('M', W - 2);
        char sh[64]; int segc = -1; int e0 = 0; printf("n = %lld\n", n);
        for (int r = 1; r <= 3000; r++) { do_round(); if (halted || bad) break; shape(sh);
            int alive = 0, ok = 0, mm = 0; for (int q = 0; q < nm; q++) if (A[q]) { alive++; if (T[q] == 'M') { mm++; if (P[q] == W - 2) ok = 1; } }
            if (nend > e0) { printf("   round %2d seg %d %-8s end meetings h:", r, segc, sh); for (int q = e0; q < nend; q++) printf(" %.1f", log2((double)W / (endd[q] > 0 ? endd[q] : 1))); printf("\n"); e0 = nend; }
            if (alive == 2 && ok) { printf("   clean after round %d, next n = %lld\n", r, (W - 6) / 2); break; }
            if (alive == 3 && ok && mm == 2) { segc++; printf("   round %2d: GMM state #%d, m/E = %.4f\n", r, segc, (double)0 + 0); }
        }
    }
}
