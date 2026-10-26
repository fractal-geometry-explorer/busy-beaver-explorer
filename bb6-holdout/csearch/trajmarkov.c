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
/* returns next n (or -1 halt, -2 bad/too long); fills rounds */
static ll cycle(ll n, int *rounds) {
    nm = 0; halted = 0; bad = 0; nend = 0; W = 2 * n + 6;
    add('G', 1); add('M', W - 2);
    for (int r = 1; r <= 5000; r++) {
        /* the round starts with the gap at 1; do_round adds the next G at 1 */
        do_round();
        if (halted) { *rounds = r; return -1; }
        if (bad) { *rounds = r; return -2; }
        int alive = 0, ok = 0; for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M' && P[i] == W - 2) ok = 1; }
        if (alive == 2 && ok) { *rounds = r; return (W - 6) / 2; }
    }
    *rounds = 5000; return -2;
}
static ll pred(ll d) { return (d % 4 == 2) ? (d - 2) / 2 : d / 2 + 4; }
static int chain_len(void) {
    int best = nend > 0 ? 1 : 0, cur = 1;
    for (int i = 1; i < nend; i++) { if (endd[i] == pred(endd[i-1])) { cur++; if (cur > best) best = cur; } else cur = 1; }
    return best;
}


static unsigned long long s[2];
static unsigned long long rnd(void) { unsigned long long s1 = s[0]; const unsigned long long s0 = s[1]; s[0] = s0;
    s1 ^= s1 << 23; s[1] = s1 ^ s0 ^ (s1 >> 17) ^ (s0 >> 26); return s[1] + s0; }

int main(int argc, char **argv) {
    ll n = atoll(argv[1]); long long N = atoll(argv[2]); int K = atoi(argv[3]); s[0] = 77; s[1] = 0x9E3779B97F4A7C15ULL;
    int M = 1 << K;
    static double Pm[1024][1024]; static long long rc[1024], tv[1024];
    for (long long it = 0; it < N; it++) {
        int r; ll m = cycle(n, &r); tv[n & (M - 1)]++; n = m;
        ll q = (ll)(rnd() >> 24) | (1LL << 39); ll m2 = cycle(q, &r); if (m2 < 0) continue;
        int a = q & (M - 1), b = m2 & (M - 1); Pm[a][b] += 1; rc[a]++;
    }
    for (int a = 0; a < M; a++) for (int b = 0; b < M; b++) Pm[a][b] = rc[a] ? Pm[a][b] / rc[a] : 0;
    static double pi[1024], nx[1024]; for (int a = 0; a < M; a++) pi[a] = 1.0 / M;
    for (int it = 0; it < (M > 300 ? 3000 : 20000); it++) { for (int b = 0; b < M; b++) nx[b] = 0; for (int a = 0; a < M; a++) for (int b = 0; b < M; b++) nx[b] += pi[a] * Pm[a][b];
        for (int b = 0; b < M; b++) pi[b] = 0.5 * pi[b] + 0.5 * nx[b]; }
    double tvd = 0; for (int a = 0; a < M; a++) tvd += fabs(pi[a] - (double)tv[a] / N); tvd /= 2;
    printf("mod 2^%d: total variation distance between the Markov chain's stationary law and the trajectory's visits: %.4f\n", K, tvd);
    if (K <= 4) for (int a = 0; a < M; a++) printf("   %2d  stationary %.4f  trajectory %.4f\n", a, pi[a], (double)tv[a] / N);
    double mx = 0, mn = 1e9; for (int a = 0; a < M; a++) { double r = pi[a] * M; if (r > mx) mx = r; if (r < mn && r > 0) mn = r; }
    printf("   stationary law / uniform ranges from %.3f to %.3f\n", mn, mx);
    { int z = 0, zt = 0, small = 0; for (int a = 0; a < M; a++) { if (pi[a] < 1e-7) z++; if (tv[a] == 0) zt++; if (pi[a] * M < 0.1) small++; }
      printf("   residues with stationary weight < 1e-7: %d of %d; never visited by the trajectory sample: %d; weight under a tenth of uniform: %d\n", z, M, zt, small); }
}
