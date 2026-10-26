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
    long long N = atoll(argv[1]); int K = atoi(argv[2]); s[0] = 12345 + atoll(argv[3]); s[1] = 0xD1B54A32D192ED03ULL;
    double g[5] = {21395686159., 412072778788., 1527835310093., 2817122580142., 3359928725359.};
    long long npass = 0, ndrop = 0;
    for (long long it = 0; it < N; it++) {
        ll E = ((ll)1 << K) | (ll)(rnd() >> (64 - K + 2)); E |= 1;
        ll x[4]; for (int i = 0; i < 4; i++) { double f = g[i] / g[4] * (1.0 + 0.02 * ((double)(rnd() >> 11) / 9007199254740992.0 - 0.5)); x[i] = (ll)(f * E); if ((x[i] & 1) != (i % 2 == 0)) x[i]++; }
        if (x[0] < 6) x[0] = 7;
        nm = 0; halted = 0; bad = 0; nend = 0; nout = 0; W = E; add('G', 1); for (int i = 0; i < 4; i++) add('W', x[i]);
        char sh[64]; int ok = 1;
        for (int r = 0; r < 0 && ok; r++) { do_round(); if (halted || bad) { ok = 0; break; } shape(sh); if (strcmp(sh, PSH[r])) ok = 0; }
        if (!ok) continue;
        npass++;
        int o0 = nout; char hist[16][64]; int nh = 0; int found = 0;
        for (int r = 0; r < 12; r++) { do_round(); if (halted || bad) break; shape(sh); strcpy(hist[nh++], sh);
            if (!strcmp(sh, "GWWWW")) break;
            if (!strcmp(sh, "GWWW")) { found = 1; break; } }
        if (!found) continue;
        int o1 = nout; int ok2 = 1;
        for (int r = 0; r < 8; r++) { do_round(); if (halted || bad) { ok2 = 0; break; } shape(sh); if (strcmp(sh, CYC[r])) { ok2 = 0; break; } }
        if (!ok2) continue;
        ndrop++;
        printf("route:"); for (int i = 0; i < nh; i++) printf(" %s", hist[i]); printf(" | outs:"); for (int i = o0; i < o1; i++) printf("%d", outs[i]); printf(" | plain outs:"); for (int i = o1; i < nout; i++) printf("%d", outs[i]); printf("\n");
    }
    fprintf(stderr, "samples %lld, P passes %lld, drops followed by a plain pass %lld\n", N, npass, ndrop);
}
