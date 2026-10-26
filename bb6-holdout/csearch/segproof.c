/* Rigorous 2-adic refinement of the clean-tape cycle (C port of rec/nrefine.py).
   Class n = rho (mod 2^k), n = 2^k j + rho with j large: every position is a*j + b.  A swap/merge test is decided
   when a = 0 (mod 4); otherwise the class is split on the next binary digit of n.  A settled class has the same
   cycle for every large j: jump, rounds and longest right-end chain (model.c's definition).
   Usage: nref K_max [cap]   -> one line per digit level; settled classes with chain >= 8 are listed. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long long ll;
typedef struct { ll a, b; } Q;
static ll jreq;   /* smallest j for which every comparison made so far comes out as in the symbolic run */
static inline void need_j(ll v) { if (v > jreq) jreq = v; }
static inline int qcmp(Q x, Q y) {
    if (x.a != y.a) {
        ll d = y.a - x.a, D = y.b - x.b;           /* actual difference y - x = d*j + D; symbolic sign = sign(d) */
        ll t = d > 0 ? -D : D, ad = d > 0 ? d : -d;  /* need ad*j > t */
        if (t >= 0) need_j(t / ad + 1);
        return x.a < y.a ? -1 : 1;
    }
    if (x.b != y.b) return x.b < y.b ? -1 : 1; return 0;
}
static inline Q qadd(Q x, ll c) { x.b += c; return x; }
#define MAXM 256
static char T[MAXM]; static Q P[MAXM]; static int A[MAXM]; static int nm;
static Q W; static int halted, bad, need; static int curseg; static int segof[8192];
static Q endd[8192]; static int endr[8192]; static int nend;
static ll minsep[3][4][4]; static ll minsep_n[3][4][4], CURN;
static int ti(char t) { return t == 'G' ? 0 : t == 'M' ? 1 : t == 'W' ? 2 : 3; }
static const int LENT[4] = {3, 2, 2, 3};
static void probe(int phase) {   /* separations between neighbouring marks, evaluated at j = 1 (the smallest member) */
    int idx[MAXM], k = 0;
    for (int i = 0; i < nm; i++) if (A[i]) idx[k++] = i;
    for (int i = 1; i < k; i++) { int v = idx[i], j = i - 1;
        while (j >= 0 && (P[idx[j]].a > P[v].a || (P[idx[j]].a == P[v].a && P[idx[j]].b > P[v].b))) { idx[j + 1] = idx[j]; j--; } idx[j + 1] = v; }
    for (int i = 0; i + 1 < k; i++) {
        int a = idx[i], b = idx[i + 1];
        ll sp = (P[b].a + P[b].b) - (P[a].a + P[a].b + LENT[ti(T[a])]);
        int x = ti(T[a]), y = ti(T[b]);
        if (sp < minsep[phase][x][y]) { minsep[phase][x][y] = sp; minsep_n[phase][x][y] = CURN; }
    }
}
static int add(char t, Q p) { for (int i = 0; i < nm; i++) if (!A[i]) { T[i] = t; P[i] = p; A[i] = 1; return i; }
    if (nm >= MAXM) { bad = 9; return 0; } T[nm] = t; P[nm] = p; A[nm] = 1; return nm++; }
static int first_right(Q x) { int b = -1; for (int i = 0; i < nm; i++) if (A[i] && qcmp(P[i], x) > 0 && (b < 0 || qcmp(P[i], P[b]) < 0)) b = i; return b; }
static int last_mark(void) { int b = -1; for (int i = 0; i < nm; i++) if (A[i] && (b < 0 || qcmp(P[i], P[b]) > 0)) b = i; return b; }
static int packet_back(Q x) {
    probe(2);
    int b = -1; for (int i = 0; i < nm; i++) if (A[i] && qcmp(P[i], x) < 0 && T[i] != 'M' && (b < 0 || qcmp(P[i], P[b]) > 0)) b = i;
    if (b < 0) return -1;
    if (T[b] == 'B') { halted = 1; return -1; }
    if (T[b] == 'G') { P[b].b += 2; return b; }
    Q q = P[b]; T[b] = 'M'; P[b] = qadd(q, -1); return add('G', qadd(q, 1));
}
static int shift_from(Q x) {
    probe(1);
    int k = first_right(x);
    if (k < 0) { W.b += 2; add('M', qadd(W, -2)); return packet_back(qadd(W, -2)); }
    if (T[k] == 'M') { T[k] = 'G'; return k; }
    if (T[k] == 'W') { T[k] = 'B'; return packet_back(P[k]); }
    if (T[k] == 'B') { T[k] = 'W'; P[k].b += 2; return packet_back(P[k]); }
    bad = 2; return -1;
}
static void do_round(void) {
    int gap = -1; for (int i = 0; i < nm; i++) if (A[i] && T[i] == 'G' && qcmp(P[i], (Q){0, 1}) == 0) gap = i;
    while (gap >= 0 && !halted && !bad && !need) {
        probe(0);
        Q g = P[gap]; int m = first_right(g);
        if (m < 0) { A[gap] = 0; W.b += 3; add('M', qadd(W, -2)); gap = packet_back(qadd(W, -2)); continue; }
        if (T[m] == 'M') {
            Q d = { P[m].a - g.a, P[m].b - g.b - 3 };
            if (d.a % 4) { need = 1; return; }
            int r4 = (int)(((d.b % 4) + 4) % 4);
            if (d.a > 0 && d.b < 0) need_j((-d.b + d.a - 1) / d.a);   /* the integer distance must not be negative */
            if (d.a < 0 || (d.a == 0 && d.b < 0) || (r4 & 1)) { bad = 3; return; }
            if (m == last_mark() && nend < 8192) { segof[nend] = curseg; endd[nend] = d; endr[nend++] = r4; }
            Q h = { d.a / 2, d.b / 2 };
            if (r4 == 0) { P[m] = (Q){ g.a + h.a, g.b + h.b - 1 }; P[gap] = (Q){ g.a + h.a, g.b + h.b + 1 }; }
            else { A[gap] = 0; T[m] = 'W'; P[m] = (Q){ g.a + h.a, g.b + h.b + 3 }; gap = packet_back(P[m]); }
        } else if (T[m] == 'W') { Q x = P[m]; A[gap] = 0; A[m] = 0; gap = shift_from(x); }
        else if (T[m] == 'B') { T[m] = 'W'; P[m].b -= 1; gap = shift_from(P[m]); }
        else { bad = 4; return; }
    }
    if (halted || bad || need) return;
    ll extra = 2;
    for (int i = 0; i < nm; i++) if (A[i] && T[i] == 'M' && qcmp(P[i], (Q){0, 0}) == 0) { T[i] = 'W'; P[i].b = 1; extra = 4; }
    for (int i = 0; i < nm; i++) if (A[i]) P[i].b += extra;
    W.b += extra; add('G', (Q){0, 1});
}

/* Segments of a clean-tape cycle: segment 0 runs from the first GMM state (gap at 1, one marker, end marker) to the
   next one or to the clean tape; segment 1 to the one after.  For every residue class, follow the symbolic cycle until
   segment SMAX ends, splitting on undecided tests.  Report, per segment, the largest possible h = log2(E / d) over its
   end meetings, for every member n = 2^k j + rho with j >= 1 (and j >= the class's j_min). */
static int SMAX, KCAP; static double best[8]; static ll bestrho[8]; static int bestk[8]; static long long leaves, capped, consts;
static void walk(int k, ll rho) {
    nm = 0; halted = bad = need = 0; nend = 0; jreq = 0; curseg = -1;
    W = (Q){ 1LL << (k + 1), 2 * rho + 6 };
    add('G', (Q){0, 1}); add('M', qadd(W, -2));
    int done = 0;
    for (int r = 1; r <= 20000 && !done; r++) {
        do_round();
        if (need) break;
        if (halted || bad) { printf("class %lld mod 2^%d: halted %d bad %d\n", rho, k, halted, bad); return; }
        int alive = 0, endm = 0, mm = 0; Q e = qadd(W, -2);
        for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M') { mm++; if (qcmp(P[i], e) == 0) endm = 1; } }
        if (alive == 2 && endm) { done = 1; break; }                 /* clean tape */
        if (alive == 3 && endm && mm == 2) { curseg++; if (curseg > SMAX) { done = 1; break; } }
    }
    if (!done && need) {
        if (k >= KCAP) { capped++; return; }
        walk(k + 1, rho); walk(k + 1, rho + (1LL << k)); return;
    }
    leaves++;
    ll j0 = jreq > 1 ? jreq : 1;
    for (int i = 0; i < nend; i++) {
        int sg = segof[i]; if (sg < 0 || sg > SMAX) continue;
        Q d = endd[i]; double h;
        if (d.a == 0) { consts++; h = 999; }
        else {
            double E1 = (double)W.a * j0 + W.b, d1 = (double)d.a * j0 + d.b;
            double hj = d1 > 0 ? log2(E1 / d1) : 999, hl = log2((double)W.a / d.a);
            h = hj > hl ? hj : hl;
        }
        if (h > best[sg]) { best[sg] = h; bestrho[sg] = rho; bestk[sg] = k; }
    }
}
int main(int argc, char **argv) {
    SMAX = atoi(argv[1]); KCAP = atoi(argv[2]);
    for (int a = 0; a < 3; a++) for (int x = 0; x < 4; x++) for (int y = 0; y < 4; y++) minsep[a][x][y] = 1LL << 62;
    walk(1, 0); walk(1, 1);
    printf("segments 0..%d, depth cap %d: %lld classes finished, %lld still open at the cap, %lld constant end distances\n", SMAX, KCAP, leaves, capped, consts);
    for (int s = 0; s <= SMAX; s++) printf("  segment %d: largest h %.3f (class %lld mod 2^%d)\n", s, best[s], bestrho[s], bestk[s]);
}
