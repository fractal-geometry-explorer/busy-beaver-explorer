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
static inline int qcmp(Q x, Q y) { if (x.a != y.a) return x.a < y.a ? -1 : 1; if (x.b != y.b) return x.b < y.b ? -1 : 1; return 0; }
static inline Q qadd(Q x, ll c) { x.b += c; return x; }
#define MAXM 256
static char T[MAXM]; static Q P[MAXM]; static int A[MAXM]; static int nm;
static Q W; static int halted, bad, need;
static Q endd[8192]; static int endr[8192]; static int nend;
static int add(char t, Q p) { for (int i = 0; i < nm; i++) if (!A[i]) { T[i] = t; P[i] = p; A[i] = 1; return i; }
    if (nm >= MAXM) { bad = 9; return 0; } T[nm] = t; P[nm] = p; A[nm] = 1; return nm++; }
static int first_right(Q x) { int b = -1; for (int i = 0; i < nm; i++) if (A[i] && qcmp(P[i], x) > 0 && (b < 0 || qcmp(P[i], P[b]) < 0)) b = i; return b; }
static int last_mark(void) { int b = -1; for (int i = 0; i < nm; i++) if (A[i] && (b < 0 || qcmp(P[i], P[b]) > 0)) b = i; return b; }
static int packet_back(Q x) {
    int b = -1; for (int i = 0; i < nm; i++) if (A[i] && qcmp(P[i], x) < 0 && T[i] != 'M' && (b < 0 || qcmp(P[i], P[b]) > 0)) b = i;
    if (b < 0) return -1;
    if (T[b] == 'B') { halted = 1; return -1; }
    if (T[b] == 'G') { P[b].b += 2; return b; }
    Q q = P[b]; T[b] = 'M'; P[b] = qadd(q, -1); return add('G', qadd(q, 1));
}
static int shift_from(Q x) {
    int k = first_right(x);
    if (k < 0) { W.b += 2; add('M', qadd(W, -2)); return packet_back(qadd(W, -2)); }
    if (T[k] == 'M') { T[k] = 'G'; return k; }
    if (T[k] == 'W') { T[k] = 'B'; return packet_back(P[k]); }
    if (T[k] == 'B') { T[k] = 'W'; P[k].b += 2; return packet_back(P[k]); }
    bad = 2; return -1;
}
static void do_round(void) {
    int gap = -1; for (int i = 0; i < nm; i++) if (A[i] && T[i] == 'G' && P[i].a == 0 && P[i].b == 1) gap = i;
    while (gap >= 0 && !halted && !bad && !need) {
        Q g = P[gap]; int m = first_right(g);
        if (m < 0) { A[gap] = 0; W.b += 3; add('M', qadd(W, -2)); gap = packet_back(qadd(W, -2)); continue; }
        if (T[m] == 'M') {
            Q d = { P[m].a - g.a, P[m].b - g.b - 3 };
            if (d.a % 4) { need = 1; return; }
            int r4 = (int)(((d.b % 4) + 4) % 4);
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
    for (int i = 0; i < nm; i++) if (A[i] && T[i] == 'M' && P[i].a == 0 && P[i].b == 0) { T[i] = 'W'; P[i].b = 1; extra = 4; }
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
    nm = 0; halted = bad = need = 0; nend = 0;
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
int main(int argc, char **argv) {
    int K = atoi(argv[1]); long long cap = argc > 2 ? atoll(argv[2]) : 200000000LL;
    ll *cur = malloc(sizeof(ll) * 2); long long nc = 2; cur[0] = 0; cur[1] = 1;   /* classes mod 2^1 */
    int cummax = 0; long double dens[64] = {0};
    for (int k = 1; k <= K && nc > 0; k++) {
        ll *nx = malloc(sizeof(ll) * (size_t)(2 * nc + 2)); long long nn = 0, settled = 0, other = 0;
        int newmax = 0; long long hist[64] = {0};
        for (long long i = 0; i < nc; i++) {
            ll rho = cur[i], jump; int rounds, chain;
            int s = cycle(k, rho, &jump, &rounds, &chain);
            if (s == 1) { if (nn + 2 > 2 * nc + 2) { fprintf(stderr, "overflow\n"); return 1; } nx[nn++] = rho; nx[nn++] = rho + (1LL << k); continue; }
            if (s == 0) {
                settled++; if (chain > 63) chain = 63; hist[chain]++; dens[chain] += 1.0L / (long double)(1ULL << k);
                if (chain > newmax) newmax = chain;
                if (chain >= 8) printf("  chain %d: n = %lld (mod 2^%d), jump %lld, %d rounds\n", chain, rho, k, jump, rounds);
            } else { other++; printf("  class n = %lld (mod 2^%d): %s\n", rho, k, s == 2 ? "HALTS" : s == 3 ? "contact/bad" : "too long"); }
        }
        if (newmax > cummax) cummax = newmax;
        printf("digits %2d: settled %lld, still open %lld, longest chain settled here %d (overall %d); chain counts:", k, settled, nn / 2, newmax, cummax);
        for (int c = 0; c < 64; c++) if (hist[c]) printf(" %d:%lld", c, hist[c]);
        printf("\n"); fflush(stdout);
        free(cur); cur = nx; nc = nn;
        if (nc > cap) { printf("stopping: %lld open classes exceed the cap\n", nc); break; }
    }
    printf("density of settled n by chain length:");
    for (int c = 0; c < 64; c++) if (dens[c] > 0) printf(" %d:%.3Le", c, dens[c]);
    printf("\n");
    return 0;
}
