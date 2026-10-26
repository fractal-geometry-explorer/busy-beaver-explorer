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
static ll endd[4096]; static int endround[4096]; static int nend; static int CURR;
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
            if (m == last_mark() && nend < 4096) { endround[nend] = CURR; endd[nend++] = d; }
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

static ll pred(ll d) { return (d % 4 == 2) ? (d - 2) / 2 : d / 2 + 4; }
static long long runhist[64], stretchhist[8];
int main(int argc, char **argv) {
    long long N = atoll(argv[1]); int bits = atoi(argv[2]); unsigned long long seed = argc > 3 ? atoll(argv[3]) : 12345;
    static char sh[6000][16]; static int isps[6000];
    long long runs_with_loop = 0, runs_two = 0, runs_total = 0;
    for (long long t = 0; t < N; t++) {
        seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17;
        ll n = (ll)((seed >> (64 - bits)) | (1ULL << (bits - 1)));
        n = n / 6 * 6 + 2;
        nm = 0; halted = 0; bad = 0; nend = 0; W = 2 * n + 6; add('G', 1); add('M', W - 2);
        int R = 0;
        for (int r = 0; r < 5000; r++) {
            shape(sh[R]); R++; CURR = r;
            do_round();
            if (halted || bad) break;
            int alive = 0, ok = 0; for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M' && P[i] == W - 2) ok = 1; }
            if (alive == 2 && ok) { shape(sh[R]); R++; break; }
        }
        /* pass starts: GWWW, GBW, GMB at rounds i, i+1, i+2 (round index = state before round i) */
        for (int i = 0; i < R; i++) isps[i] = (i + 2 < R && !strcmp(sh[i], "GWWW") && !strcmp(sh[i+1], "GBW") && !strcmp(sh[i+2], "GMB"));
        /* maximal runs of pred-chained end meetings */
        int a = 0;
        while (a < nend) {
            int b = a; while (b + 1 < nend && endd[b + 1] == pred(endd[b])) b++;
            int len = b - a + 1; runs_total++; runhist[len < 63 ? len : 63]++;
            /* loop stretches inside the run's round span: groups of pass starts 8 rounds apart */
            int r0 = endround[a], r1 = endround[b]; int stretches = 0, last = -100;
            for (int i = r0; i <= r1 && i < R; i++) if (isps[i]) { if (i - last != 8) stretches++; last = i; }
            stretchhist[stretches < 7 ? stretches : 7]++;
            if (stretches >= 1) runs_with_loop++;
            if (stretches >= 2) { runs_two++; printf("run with %d loop stretches: n = %lld, %d meetings, rounds %d-%d\n", stretches, n, len, r0, r1); fflush(stdout); }
            a = b + 1;
        }
    }
    printf("%lld runs from %lld samples of %d-bit n; %lld contain a loop stretch, %lld contain two or more\n", runs_total, N, bits, runs_with_loop, runs_two);
    printf("run lengths:"); for (int i = 0; i < 64; i++) if (runhist[i]) printf(" %d:%lld", i, runhist[i]); printf("\n");
    printf("stretches per run:"); for (int i = 0; i < 8; i++) if (stretchhist[i]) printf(" %d:%lld", i, stretchhist[i]); printf("\n");
    return 0;
}
