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
static Q W; static int halted, bad, need;
static Q endd[8192]; static int endr[8192]; static int nend;
static ll minsep[3][4][4]; static ll minsep_n[3][4][4], CURN;
static int ti(char t) { return t == 'G' ? 0 : t == 'M' ? 1 : t == 'W' ? 2 : 3; }
static const int LENT[4] = {3, 2, 2, 3};
static ll dsep[3][4][4], dsep_da[3][4][4]; static int nthin, KK; static ll lvl_left[64], lvl_other[64], lvl_other_da[64];
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
        if (P[a].a != P[b].a && sp < dsep[phase][x][y]) { dsep[phase][x][y] = sp; dsep_da[phase][x][y] = P[b].a - P[a].a; }
        if (P[a].a != P[b].a) { int left = (T[a] == 'G' && P[a].a == 0 && P[a].b == 1);
            if (left) { if (sp < lvl_left[KK]) lvl_left[KK] = sp; } else if (sp < lvl_other[KK]) { lvl_other[KK] = sp; lvl_other_da[KK] = P[b].a - P[a].a; } }
        if (0) { nthin++;
            fprintf(stderr, "THIN class %lld mod 2^%d (smallest member %lld): phase %d, %c at %lld j + %lld then %c at %lld j + %lld, separation at j=1: %lld; marks:", CURN - (1LL << KK), KK, CURN, phase, T[a], P[a].a, P[a].b, T[b], P[b].a, P[b].b, sp);
            for (int i = 0; i < k; i++) fprintf(stderr, " %c(%lld,%lld)", T[idx[i]], P[idx[i]].a, P[idx[i]].b); fprintf(stderr, " W(%lld,%lld)\n", W.a, W.b); }
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
            if (m == last_mark() && nend < 8192) { endd[nend] = d; endr[nend++] = r4; }
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
static int chain_len(void) {
    int best = nend > 0 ? 1 : 0, cur = 1;
    for (int i = 1; i < nend; i++) {
        Q p = endr[i-1] == 2 ? (Q){ endd[i-1].a / 2, (endd[i-1].b - 2) / 2 } : (Q){ endd[i-1].a / 2, endd[i-1].b / 2 + 4 };
        if (qcmp(endd[i], p) == 0) { cur++; if (cur > best) best = cur; } else cur = 1;
    }
    return best;
}
/* 0 settled, 1 split, 2 halt, 3 bad, 4 too long */
static int cycle(int k, ll rho, ll *jump, int *rounds, int *chain) {
    KK = k;
    nm = 0; halted = bad = need = 0; nend = 0; jreq = 0;
    W = (Q){ 1LL << (k + 1), 2 * rho + 6 };
    add('G', (Q){0, 1}); add('M', qadd(W, -2));
    for (int r = 1; r <= 20000; r++) {
        do_round();
        if (need) return 1;
        if (halted) return 2;
        if (bad) return 3;
        int alive = 0, ok = 0; Q e = qadd(W, -2);
        for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M' && qcmp(P[i], e) == 0) ok = 1; }
        if (alive == 2 && ok) { *jump = (W.b - (2 * rho + 6)) / 2; *rounds = r; *chain = chain_len(); return 0; }
    }
    return 4;
}
static int cycle_int(ll n, ll *jump, int *rounds, int *chain) {
    nm = 0; halted = bad = need = 0; nend = 0; jreq = 0;
    W = (Q){ 0, 2 * n + 6 };
    add('G', (Q){0, 1}); add('M', qadd(W, -2));
    for (int r = 1; r <= 20000; r++) {
        do_round();
        if (need) return 1;
        if (halted) return 2;
        if (bad) return 3;
        int alive = 0, ok = 0; Q e = qadd(W, -2);
        for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M' && qcmp(P[i], e) == 0) ok = 1; }
        if (alive == 2 && ok) { *jump = (W.b - (2 * n + 6)) / 2; *rounds = r; *chain = chain_len(); return 0; }
    }
    return 4;
}
int main(int argc, char **argv) {
    for (int p = 0; p < 3; p++) for (int x = 0; x < 4; x++) for (int y = 0; y < 4; y++) { minsep[p][x][y] = 1LL << 62; dsep[p][x][y] = 1LL << 62; }
    for (int i = 0; i < 64; i++) lvl_left[i] = lvl_other[i] = 1LL << 62;
    int K = atoi(argv[1]); long long cap = argc > 2 ? atoll(argv[2]) : 200000000LL;
    ll *cur = malloc(sizeof(ll) * 2); long long nc = 2; cur[0] = 0; cur[1] = 1;   /* classes mod 2^1 */
    int cummax = 0; long double dens[64] = {0};
    for (int k = 1; k <= K && nc > 0; k++) {
        ll *nx = malloc(sizeof(ll) * (size_t)(2 * nc + 2)); long long nn = 0, settled = 0, other = 0;
        int newmax = 0; long long hist[64] = {0}; long long direct = 0, dbad = 0; int dmax = 0; ll dmax_n = 0; long long jh[64] = {0}; ll jmax = 0, jmax_rho = 0;
        for (long long i = 0; i < nc; i++) {
            ll rho = cur[i], jump; int rounds, chain;
            static ll save[3][4][4], saven[3][4][4], saved[3][4][4], savedd[3][4][4]; memcpy(save, minsep, sizeof minsep); memcpy(saven, minsep_n, sizeof minsep_n); memcpy(saved, dsep, sizeof dsep); memcpy(savedd, dsep_da, sizeof dsep_da);
            CURN = rho + (1LL << k);   /* the smallest member with j = 1 */
            int s = cycle(k, rho, &jump, &rounds, &chain);
            if (s != 0) { memcpy(minsep, save, sizeof minsep); memcpy(minsep_n, saven, sizeof minsep_n); memcpy(dsep, saved, sizeof dsep); memcpy(dsep_da, savedd, sizeof dsep_da); }
            if (s == 1) {   /* open class: its only member with k+1 binary digits is rho + 2^k; run it directly */
                ll n = rho + (1LL << k), dj; int dr, dc; CURN = n; int ds = cycle_int(n, &dj, &dr, &dc); direct++;
                if (ds != 0) { dbad++; printf("  DIRECT n = %lld: %s\n", n, ds == 2 ? "HALTS" : ds == 3 ? "bad" : "too long"); }
                else if (dc > dmax) { dmax = dc; dmax_n = n; }
            }
            if (s == 1) { if (nn + 2 > 2 * nc + 2) { fprintf(stderr, "overflow\n"); return 1; } nx[nn++] = rho; nx[nn++] = rho + (1LL << k); continue; }
            if (s == 0) {
                settled++; { int bkt = 0; ll x = jreq; while (x > 0) { bkt++; x >>= 1; } jh[bkt]++; if (jreq > jmax) { jmax = jreq; jmax_rho = rho; } if (jreq >= 2) fprintf(stderr, "%d %lld %lld %lld %d %d\n", k, rho, jreq, jump, rounds, chain); }
                if (chain > 63) chain = 63; hist[chain]++; dens[chain] += 1.0L / (long double)(1ULL << k);
                if (chain > newmax) newmax = chain;
                
            } else { other++; printf("  class n = %lld (mod 2^%d): %s\n", rho, k, s == 2 ? "HALTS" : s == 3 ? "contact/bad" : "too long"); }
        }
        if (newmax > cummax) cummax = newmax;
        printf("digits %2d: settled %lld, still open %lld, longest chain settled here %d (overall %d); chain counts:", k, settled, nn / 2, newmax, cummax);
        for (int c = 0; c < 64; c++) if (hist[c]) printf(" %d:%lld", c, hist[c]);
        printf("\n   j_min (by bit length: 0 means j >= 0 works, b means j_min < 2^b):"); for (int c = 0; c < 64; c++) if (jh[c]) printf(" %d:%lld", c, jh[c]);
        printf("  largest j_min %lld (class %lld)\n   direct runs of the %lld open-class members with %d digits: all close cleanly: %s; longest chain %d (n = %lld)\n", jmax, jmax_rho, direct, k + 1, dbad ? "NO" : "yes", dmax, dmax_n); fflush(stdout);
        free(cur); cur = nx; nc = nn;
        if (nc > cap) { printf("stopping: %lld open classes exceed the cap\n", nc); break; }
    }
    { const char *ph[3] = {"gap", "shift", "packet"}, *nmT = "GMWB"; printf("closest approaches (all settled classes at j = 1, and all direct runs):\n");
      for (int p = 0; p < 3; p++) for (int x = 0; x < 4; x++) for (int y = 0; y < 4; y++)
        if (minsep[p][x][y] < (1LL << 62)) printf("  %s %c%c min %lld (n=%lld)\n", ph[p], nmT[x], nmT[y], minsep[p][x][y], minsep_n[p][x][y]); }
    { const char *ph[3] = {"gap", "shift", "packet"}, *nmT = "GMWB"; printf("closest approach of neighbours with different j-coefficients, at j = 1 (settled classes only):\n");
      for (int p = 0; p < 3; p++) for (int x = 0; x < 4; x++) for (int y = 0; y < 4; y++)
        if (dsep[p][x][y] < (1LL << 62)) printf("  %s %c%c min %lld (coefficient gap %lld)\n", ph[p], nmT[x], nmT[y], dsep[p][x][y], dsep_da[p][x][y]); }
    for (int i = 1; i < 64; i++) if (lvl_other[i] < (1LL << 62)) printf("depth %2d: gap at cell 1 vs next mark: min %lld;  all other differently scaling neighbours: min %lld (coefficient gap %lld)\n", i, lvl_left[i], lvl_other[i], lvl_other_da[i]);
    printf("density of settled n by chain length:");
    for (int c = 0; c < 64; c++) if (dens[c] > 0) printf(" %d:%.3Le", c, dens[c]);
    printf("\n");
    return 0;
}
