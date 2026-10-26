/* Mark model of 1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE (same rules as tracecycle.py), for fast sweeps.
   For each n: next clean n, rounds, and the meetings between a gap and the end marker (the right-end cascade). */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>
typedef long long ll;
#define MAXM 128
static char T[MAXM]; static ll P[MAXM]; static int A[MAXM]; static int nm;
static ll W;
static int halted, bad;
static ll endd[4096]; static int nend;
static ll minsep[3][4][4]; static ll minsep_n[3][4][4];
static ll CURN;
static int ti(char t) { return t == 'G' ? 0 : t == 'M' ? 1 : t == 'W' ? 2 : 3; }
static int LENT[4] = {3, 2, 2, 3};
static void probe(int phase) {
    int idx[MAXM], k = 0;
    for (int i = 0; i < nm; i++) if (A[i]) idx[k++] = i;
    for (int i = 1; i < k; i++) { int v = idx[i], j = i - 1; while (j >= 0 && P[idx[j]] > P[v]) { idx[j + 1] = idx[j]; j--; } idx[j + 1] = v; }
    for (int i = 0; i + 1 < k; i++) {
        int a = idx[i], b = idx[i + 1];
        ll s = P[b] - (P[a] + LENT[ti(T[a])]);
        int x = ti(T[a]), y = ti(T[b]);
        if (s < minsep[phase][x][y]) { minsep[phase][x][y] = s; minsep_n[phase][x][y] = CURN; }
    }
}
static int add(char t, ll p) { for (int i = 0; i < nm; i++) if (!A[i]) { T[i] = t; P[i] = p; A[i] = 1; return i; }
    if (nm >= MAXM) { bad = 1; return 0; } T[nm] = t; P[nm] = p; A[nm] = 1; return nm++; }
static int first_right(ll x) { int b = -1; for (int i = 0; i < nm; i++) if (A[i] && P[i] > x && (b < 0 || P[i] < P[b])) b = i; return b; }
static int last_mark(void) { int b = -1; for (int i = 0; i < nm; i++) if (A[i] && (b < 0 || P[i] > P[b])) b = i; return b; }
static int packet_back(ll x) {
    probe(2);
    int b = -1; for (int i = 0; i < nm; i++) if (A[i] && P[i] < x && T[i] != 'M' && (b < 0 || P[i] > P[b])) b = i;
    if (b < 0) return -1;
    if (T[b] == 'B') { halted = 1; return -1; }
    if (T[b] == 'G') { P[b] += 2; return b; }
    ll q = P[b]; T[b] = 'M'; P[b] = q - 1; return add('G', q + 1);
}
static int shift_from(ll x) {
    probe(1);
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
        probe(0);
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
static void dump_minsep(void) {
    const char *ph[3] = {"gap", "shift", "packet"}, *nmT = "GMWB";
    for (int p = 0; p < 3; p++) for (int x = 0; x < 4; x++) for (int y = 0; y < 4; y++)
        if (minsep[p][x][y] < (1LL << 62)) printf("  %s %c%c min %lld (n=%lld)\n", ph[p], nmT[x], nmT[y], minsep[p][x][y], minsep_n[p][x][y]);
}
int main(int argc, char **argv) {
    for (int p = 0; p < 3; p++) for (int x = 0; x < 4; x++) for (int y = 0; y < 4; y++) minsep[p][x][y] = 1LL << 62;
    if (argc > 1 && argv[1][0] == 't') {          /* follow the machine's own clean tapes: t <limit n> <seconds> */
        ll limit = atoll(argv[2]); double secs = atof(argv[3]);
        ll n = 2, cycles = 0; long long hist[64] = {0}; int bestL = 0; double bestH = 0;
        clock_t t0 = clock();
        while (n < limit) {
            CURN = n; int r; ll m = cycle(n, &r); cycles++;
            if (m < 0) { printf("STOP at n=%lld code %lld\n", n, m); break; }
            int L = chain_len(); if (L > 63) L = 63; hist[L]++;
            ll md = -1; for (int i = 1; i < nend; i++) if (md < 0 || endd[i] < md) md = endd[i];
            double h = md > 0 ? log2((double)(2 * n + 6) / md) : 0;
            if (L >= 8) { printf("deep: n=%lld chain=%d halvings=%.2f rounds=%d\n", n, L, h, r); fflush(stdout); }
            if (L > bestL || h > bestH + 0.5) { if (L > bestL) bestL = L; if (h > bestH) bestH = h;
                printf("record: n=%lld chain=%d halvings=%.2f rounds=%d\n", n, L, h, r); fflush(stdout); }
            if (m <= n) { printf("NOT INCREASING at n=%lld\n", n); break; }
            n = m;
            if ((cycles & 0xFFFFF) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > secs) break;
        }
        printf("reached n=%lld after %lld cycles\nchain lengths:", n, cycles);
        for (int i = 0; i < 64; i++) if (hist[i]) printf(" %d:%lld", i, hist[i]);
        printf("\nclosest approaches:\n"); dump_minsep();
        return 0;
    }
    ll lo = atoll(argv[1]), hi = atoll(argv[2]); int mode = argc > 3 ? atoi(argv[3]) : 0;
    double best = 0;
    for (ll n = lo; n < hi; n++) {
        int r; ll m = cycle(n, &r);
        ll md = -1; for (int i = 1; i < nend; i++) if (md < 0 || endd[i] < md) md = endd[i];
        if (mode == 1) { printf("%lld %lld %d %lld\n", n, m, r, md); continue; }
        if (mode == 3) { int L = chain_len(); if (L >= atoi(argv[4])) printf("%lld %d\n", n, L); continue; }
        if (mode == 2) { static long long hist[64]; int L = chain_len(); if (L > 63) L = 63; hist[L]++;
            if (n == hi - 1) { for (int i = 0; i < 64; i++) if (hist[i]) printf("%d %lld\n", i, hist[i]); } continue; }
        double h = md > 0 ? log2((double)(2 * n + 6) / md) : 0;
        if (m < 0 || (md >= 0 && md <= 12) || h > best || h >= 9.0) {
            if (h > best) best = h;
            printf("n=%lld next=%lld rounds=%d closest_end_d=%lld halvings=%.2f%s\n", n, m, r, md, h,
                   m == -1 ? " HALT" : (m == -2 ? " BAD" : ""));
            fflush(stdout);
        }
        if (mode == 0 && (n & ((1LL << 26) - 1)) == 0) { fprintf(stderr, "at %lld\n", n); }
    }
    return 0;
}
