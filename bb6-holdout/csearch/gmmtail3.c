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
static ll endd[4096]; static int nend; static int endr[4096]; static int curround;
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
            if (m == last_mark() && nend < 4096) { endr[nend] = curround; endd[nend++] = d; }
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

static ll pred(ll d) { return (d % 4 == 2) ? (d - 2) / 2 : d / 2 + 4; }
/* GMM round starts: gap at 1, marker at m, end marker at E - 2 (E = width, last 1 at E - 1).  Run the mark model to
   the next clean tape; report states whose right-end run reaches a meeting distance <= 2 (necessary for a halt). */

/* Random GMM round starts at width ~2^K: plane mode (m, E free) or line mode (m = n + 2, E = 2n + 11, n even, as on
   the machine's own cycles). Histogram of the closest right-end approach h = log2(E / min distance) in 1/4 halvings,
   plus the histogram of the longest chain of right-end meetings. */
static unsigned long long s[2];
static unsigned long long rnd(void) { unsigned long long s1 = s[0]; const unsigned long long s0 = s[1]; s[0] = s0;
    s1 ^= s1 << 23; s[1] = s1 ^ s0 ^ (s1 >> 17) ^ (s0 >> 26); return s[1] + s0; }
int main(int argc, char **argv) {
    int K = atoi(argv[1]); long long N = atoll(argv[2]); int line = atoi(argv[3]); s[0] = 0x9E3779B97F4A7C15ULL ^ atoll(argv[4]); s[1] = 0xD1B54A32D192ED03ULL;
    for (int i = 0; i < 20; i++) rnd();
    static long long hist[400]; static long long rh[20], rdh[200]; double HMIN = atof(getenv("HMIN") ? getenv("HMIN") : "4"); long long done_n = 0, bad_n = 0, halt_n = 0, contact_n = 0; double best = 0; ll bm = 0, bE = 0;
    for (long long it = 0; it < N; it++) {
        ll E, m;
        if (line == 1) { ll n = (ll)((rnd() >> (64 - K + 1)) | (1ULL << (K - 2))) & ~1LL; m = n + 2; E = 2 * n + 11; }
        else if (line < 0) { m = (ll)((rnd() >> (64 - K + 1)) | (1ULL << (K - 2))) & ~1LL; E = 2 * m + (-line); }
        else if (line == 0) { E = (ll)((rnd() >> (64 - K)) | (1ULL << (K - 1))) | 1; m = 6 + (ll)(rnd() % (unsigned long long)(E - 14)); m &= ~1LL; if (m < 6) m = 6; }
        else { /* line >= 2: fixed ratio rho = line / 1000 (with random offset of a few hundred) */
            E = (ll)((rnd() >> (64 - K)) | (1ULL << (K - 1))) | 1; m = (ll)((double)E * line / 1000.0) + (ll)(rnd() % 512) - 256; m &= ~1LL; }
        nm = 0; halted = 0; bad = 0; nend = 0; W = E; add('G', 1); add('M', m); add('M', W - 2);
        int contact = 0, fin = 0;
        for (int r = 1; r <= 5000; r++) {
            curround = r; do_round();
            if (halted || bad) break;
            int alive = 0, ok = 0; for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M' && P[i] == W - 2) ok = 1; }
            if (alive == 2 && ok) { fin = 1; break; }
        }
        if (halted) halt_n++; if (bad) bad_n++; if (fin) done_n++;
        ll mind = -1; for (int i = 0; i < nend; i++) if (mind < 0 || endd[i] < mind) mind = endd[i];
        int imin = -1; for (int i = 0; i < nend; i++) if (endd[i] == mind) { imin = i; break; }
        int runidx = 0; for (int i = 1; i <= imin; i++) if (endd[i] != pred(endd[i-1])) runidx++;
        if (mind > 0) { double h = log2((double)E / mind); int b = (int)(h * 4); if (b > 399) b = 399; hist[b]++;
            if (h >= HMIN) { int ri = runidx > 19 ? 19 : runidx; rh[ri]++; int rr = endr[imin] > 199 ? 199 : endr[imin]; rdh[rr]++; }
            if (h > best) { best = h; bm = m; bE = E; } }
        else if (mind == 0) hist[399]++;
    }
    printf("K %d samples %lld line %d finished %lld bad %lld halted %lld best %.2f (m %lld E %lld)\n", K, N, line, done_n, bad_n, halt_n, best, bm, bE);
    printf("states with h >= %.1f by the index of the run (0 = first) that comes closest:", HMIN); for (int i = 0; i < 20; i++) if (rh[i]) printf(" %d:%lld", i, rh[i]); printf("\n");
    printf("  by round:"); for (int i = 0; i < 200; i++) if (rdh[i]) printf(" %d:%lld", i, rdh[i]); printf("\n");
    long long tail = 0; for (int b = 399; b >= 0; b--) { tail += hist[b]; if (hist[b]) printf("h>=%.2f %lld\n", b / 4.0, tail); }
    return 0;
}
