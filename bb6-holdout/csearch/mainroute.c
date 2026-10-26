/* Mark model of 1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE (same rules as tracecycle.py), for fast sweeps.
   For each n: next clean n, rounds, and the meetings between a gap and the end marker (the right-end cascade). */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
typedef long long ll;
#define MAXM 128
static char T[MAXM]; static ll P[MAXM]; static int A[MAXM]; static int nm;
static ll W;
static int halted, bad;
static ll endd[4096]; static int nend;
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
            if (m == last_mark() && nend < 4096) endd[nend++] = d;
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

/* shape of the current configuration (sorted marks), as a short string */
static void shape(char *out) {
    int idx[MAXM], k = 0; for (int i = 0; i < nm; i++) if (A[i]) idx[k++] = i;
    for (int i = 1; i < k; i++) { int v = idx[i], j = i - 1; while (j >= 0 && P[idx[j]] > P[v]) { idx[j+1] = idx[j]; j--; } idx[j+1] = v; }
    int q = 0; for (int i = 0; i < k && q < 15; i++) out[q++] = T[idx[i]]; out[q] = 0;
}
static const char *ROUTE[7] = {"GMM", "GMMM", "GMMW", "GMWW", "GWWW", "GBW", "GMB"};
static long long hist[2000][40];
int main(int argc, char **argv) {
    long long N = atoll(argv[1]); int bits = atoi(argv[2]); unsigned long long seed = argc > 3 ? atoll(argv[3]) : 12345;
    const unsigned long long TS = 1ULL << 40;
    /* tau* = -38423/1225 mod 2^40 */
    unsigned long long inv = 1; for (int it = 0; it < 7; it++) inv = inv * (2 - 1225ULL * inv);
    unsigned long long tstar = (unsigned long long)(-(long long)38423) * inv;   /* mod 2^64; low 40 bits matter */
    char sh[6000][16]; ll Ws[6000];
    long long entries = 0;
    for (long long t = 0; t < N; t++) {
        seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17;
        ll n = (ll)((seed >> (64 - bits)) | (1ULL << (bits - 1)));
        n = n / 6 * 6 + 2;                  /* even, 2 mod 3 */
        nm = 0; halted = 0; bad = 0; nend = 0; W = 2 * n + 6; add('G', 1); add('M', W - 2);
        int R = 0;
        for (int r = 0; r < 5000; r++) {
            shape(sh[R]); Ws[R] = W; R++;
            do_round();
            if (halted || bad) break;
            int alive = 0, ok = 0; for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M' && P[i] == W - 2) ok = 1; }
            if (alive == 2 && ok) { shape(sh[R]); Ws[R] = W; R++; break; }
        }
        for (int i = 0; i + 6 < R; i++) {
            int okr = 1; for (int q = 0; q < 7; q++) if (strcmp(sh[i + q], ROUTE[q])) { okr = 0; break; }
            if (!okr) continue;
            ll g = Ws[i] - (2 * n + 6);
            unsigned long long x = ((unsigned long long)Ws[i] - tstar) & (TS - 1);
            int v = 0; while (v < 40 && !((x >> v) & 1)) v++;
            int G = v - 3; if (G < 0) G = 0; if (G > 39) G = 39;
            if (g >= 0 && g < 2000) hist[g][G]++;
            entries++;
            if (G >= 9) { printf("G %d at n = %lld, growth %lld, round %d\n", G, n, g, i); fflush(stdout); }
        }
    }
    printf("%lld main-route entries in %lld samples of %d-bit n\n", entries, N, bits);
    for (int g = 0; g < 2000; g++) { long long tot = 0; int mx = 0; for (int G = 0; G < 40; G++) if (hist[g][G]) { tot += hist[g][G]; mx = G; }
        if (tot) { printf("growth %4d: %8lld entries, max gap %d :", g, tot, mx); for (int G = 0; G < 40; G++) if (hist[g][G]) printf(" %d:%lld", G, hist[g][G]); printf("\n"); } }
    return 0;
}
