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

/* Universal check of two-marker (GMM) round starts: gap at 1, marker at m, end marker at E - 2, nothing else.
   Every halt of the machine from a clean tape happens inside the segment that starts at some GMM state (the part of
   a cycle up to its first GMM state is one or two fixed rounds).  For every m (even, 4 <= m <= E - 6) and odd E in a
   range, run the mark model only until the next GMM state or the clean tape, with contact detection; flag any state
   whose segment brings an end meeting within distance 2 or lets marks touch, or halts. */
static double besth[64]; static ll bestm[64], bestE[64];
int main(int argc, char **argv) {
    ll Emin = atoll(argv[1]), Emax = atoll(argv[2]);
    long long total = 0, flagged = 0, halted_model = 0, capped = 0, toGMM = 0, toClean = 0;
    for (ll E = Emin | 1; E <= Emax; E += 2) {
        for (ll m = 4; m <= E - 6; m += 2) {
            total++;
            nm = 0; halted = 0; bad = 0; nend = 0; W = E; add('G', 1); add('M', m); add('M', W - 2);
            int contact = 0, fin = 0;
            for (int r = 1; r <= 4000; r++) {
                do_round();
                if (halted) { halted_model++; break; }
                if (bad) break;
                { int idx[MAXM], k = 0; for (int i = 0; i < nm; i++) if (A[i]) idx[k++] = i;
                  for (int i = 1; i < k; i++) { int v = idx[i], j = i - 1; while (j >= 0 && P[idx[j]] > P[v]) { idx[j+1] = idx[j]; j--; } idx[j+1] = v; }
                  for (int i = 0; i + 1 < k; i++) { int a = idx[i], b = idx[i+1]; int la = (T[a] == 'G' || T[a] == 'B') ? 3 : 2;
                      if (P[b] - (P[a] + la) < 1 && !(T[a] == 'G' && T[b] == 'M')) contact = 1; } }
                int alive = 0, endm = 0, mm = 0; for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M') { mm++; if (P[i] == W - 2) endm = 1; } }
                if (alive == 2 && endm) { fin = 1; toClean++; break; }
                if (alive == 3 && endm && mm == 2) { fin = 2; toGMM++; break; }
            }
            if (!fin && !halted && !bad) capped++;
            ll mind = -1; for (int i = 0; i < nend; i++) if (mind < 0 || endd[i] < mind) mind = endd[i];
            if ((mind >= 0 && mind <= 2) || contact || halted || bad || !fin) { flagged++; printf("%lld %lld %lld %d %d %d %d\n", m, E, mind, contact, halted, bad, fin); }
            if (mind > 0) { double h = log2((double)E / mind); int b = 0; while ((2LL << b) <= E) b++;
                if (h > besth[b]) { besth[b] = h; bestm[b] = m; bestE[b] = E; } }
        }
    }
    for (int b = 0; b < 64; b++) if (besth[b] > 0) fprintf(stderr, "width 2^%d..2^%d: closest approach %.2f halvings (m = %lld, E = %lld)\n", b, b + 1, besth[b], bestm[b], bestE[b]);
    fprintf(stderr, "GMM states %lld: segment ends at a GMM state %lld, at the clean tape %lld, round cap %lld; flagged %lld, model halts %lld\n", total, toGMM, toClean, capped, flagged, halted_model);
    return 0;
}
