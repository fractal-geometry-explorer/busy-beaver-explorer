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

static ll pred(ll d) { return (d % 4 == 2) ? (d - 2) / 2 : d / 2 + 4; }
/* GMM round starts: gap at 1, marker at m, end marker at E - 2 (E = width, last 1 at E - 1).  Run the mark model to
   the next clean tape; report states whose right-end run reaches a meeting distance <= 2 (necessary for a halt). */
static double besth[64]; static ll bestm[64], bestE[64];
int main(int argc, char **argv) {
    ll Emin = atoll(argv[1]), Emax = atoll(argv[2]);
    long long total = 0, flagged = 0, halted_model = 0;
    for (ll E = Emin; E <= Emax; E++) {
        for (ll m = 6; m <= E - 8; m++) {
            /* parity: after the gap (cells 1-3), cell i is 1 iff i is even; a marker must start on a 1 cell: m even.
               after the marker (even length) the phase flips: cell i is 1 iff i odd; the end marker at E-2 must start on
               a 1: E - 2 odd -> E odd; then after it, phase flips back; last 1 at E - 1 (part of the end marker). */
            if (m % 2 || E % 2 == 0) continue;
            total++;
            nm = 0; halted = 0; bad = 0; nend = 0; W = E; add('G', 1); add('M', m); add('M', W - 2);
            int r; int done = 0; ll mind = -1;
            int contact = 0;
            for (r = 1; r <= 3000; r++) {
                do_round();
                { int idx[MAXM], k = 0; for (int i = 0; i < nm; i++) if (A[i]) idx[k++] = i;
                  for (int i = 1; i < k; i++) { int v = idx[i], j = i - 1; while (j >= 0 && P[idx[j]] > P[v]) { idx[j+1] = idx[j]; j--; } idx[j+1] = v; }
                  for (int i = 0; i + 1 < k; i++) { int a = idx[i], b = idx[i+1]; int la = (T[a] == 'G' || T[a] == 'B') ? 3 : 2;
                      if (P[b] - (P[a] + la) < 1 && !(T[a] == 'G' && T[b] == 'M')) contact = 1; } }
                if (halted) { halted_model++; break; }
                if (bad) break;
                int alive = 0, ok = 0; for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M' && P[i] == W - 2) ok = 1; }
                if (alive == 2 && ok) { done = 1; break; }
            }
            for (int i = 0; i < nend; i++) if (mind < 0 || endd[i] < mind) mind = endd[i];
            if ((mind >= 0 && mind <= 2) || contact) { flagged++; printf("%lld %lld %lld %d\n", m, E, mind, contact); }
            if (mind > 0) { double h = log2((double)E / mind); int b = 0; while ((2LL << b) <= E) b++;
                if (h > besth[b]) { besth[b] = h; bestm[b] = m; bestE[b] = E; } }
        }
    }
    for (int b = 0; b < 64; b++) if (besth[b] > 0) fprintf(stderr, "width 2^%d..2^%d: closest approach %.2f halvings (m = %lld, E = %lld)\n", b, b + 1, besth[b], bestm[b], bestE[b]);
    fprintf(stderr, "GMM states %lld, flagged (run reaches d <= 2) %lld, model halts %lld\n", total, flagged, halted_model);
    return 0;
}
