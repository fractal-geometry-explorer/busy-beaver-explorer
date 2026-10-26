/* Beam search over residue classes of n (exact class semantics, as in nrefj3.c, with 128-bit positions so classes can
   go to ~120 digits).  At each depth keep the B open classes whose right-end run is longest at the point where they
   split; report the longest chains of the classes that settle, and of the open ones.
   Usage: beamclass K B   */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
static void pr128(__int128 x);
typedef __int128 L;
typedef struct { L a, b; } Q;
static inline int qcmp(Q x, Q y) { if (x.a != y.a) return x.a < y.a ? -1 : 1; if (x.b != y.b) return x.b < y.b ? -1 : 1; return 0; }
static inline Q qadd(Q x, long long c) { x.b += c; return x; }
#define MAXM 256
static char T[MAXM]; static Q P[MAXM]; static int A[MAXM]; static int nm;
static Q W; static int halted, bad, need;
static Q endd[8192]; static int endr[8192]; static int nend;
static char SH[20000][16]; static Q SW[20000]; static int NR;
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
    int gap = -1; for (int i = 0; i < nm; i++) if (A[i] && T[i] == 'G' && qcmp(P[i], (Q){0, 1}) == 0) gap = i;
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
    long long extra = 2;
    for (int i = 0; i < nm; i++) if (A[i] && T[i] == 'M' && qcmp(P[i], (Q){0, 0}) == 0) { T[i] = 'W'; P[i].b = 1; extra = 4; }
    for (int i = 0; i < nm; i++) if (A[i]) P[i].b += extra;
    W.b += extra; add('G', (Q){0, 1});
}
static int is_pred(int i) {
    Q p = endr[i-1] == 2 ? (Q){ endd[i-1].a / 2, (endd[i-1].b - 2) / 2 } : (Q){ endd[i-1].a / 2, endd[i-1].b / 2 + 4 };
    return qcmp(endd[i], p) == 0;
}
static int chain_len(void) { int best = nend > 0 ? 1 : 0, cur = 1;
    for (int i = 1; i < nend; i++) { if (is_pred(i)) { cur++; if (cur > best) best = cur; } else cur = 1; } return best; }
static int trailing_chain(void) { if (nend == 0) return 0; int cur = 1; for (int i = nend - 1; i >= 1 && is_pred(i); i--) cur++; return cur; }
/* best halvings at the smallest member (j = 1): log2(W(1) / min end distance(1)), first meeting excluded */
static double halv(void) { double best = 0; L w = W.a + W.b;
    for (int i = 1; i < nend; i++) { L d = endd[i].a + endd[i].b; if (d > 0) { double h = log2((double)w / (double)d); if (h > best) best = h; } }
    return best; }
static void shape_now(char *out) {
    int idx[MAXM], k = 0; for (int i = 0; i < nm; i++) if (A[i]) idx[k++] = i;
    for (int i = 1; i < k; i++) { int v = idx[i], j = i - 1; while (j >= 0 && qcmp(P[idx[j]], P[v]) > 0) { idx[j+1] = idx[j]; j--; } idx[j+1] = v; }
    int q = 0; for (int i = 0; i < k && q < 15; i++) out[q++] = T[idx[i]]; out[q] = 0;
}
/* 0 settled, 1 split, 2 halt, 3 bad, 4 too long */
static int cycle(int k, L rho) {
    nm = 0; halted = bad = need = 0; nend = 0; NR = 0;
    W = (Q){ ((L)1) << (k + 1), 2 * rho + 6 };
    add('G', (Q){0, 1}); add('M', qadd(W, -2));
    for (int r = 1; r <= 19000; r++) {
        if (NR < 20000) { shape_now(SH[NR]); SW[NR] = W; NR++; }
        do_round();
        if (need) return 1; if (halted) return 2; if (bad) return 3;
        int alive = 0, ok = 0; Q e = qadd(W, -2);
        for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M' && qcmp(P[i], e) == 0) ok = 1; }
        if (alive == 2 && ok) { if (NR < 20000) { shape_now(SH[NR]); SW[NR] = W; NR++; } return 0; }
    }
    return 4;
}
static const char *ROUTE[7] = {"GMM", "GMMM", "GMMW", "GMWW", "GWWW", "GBW", "GMB"};
static unsigned long long TSTAR;
static long long stagecnt[4000][40];
static void scan_routes(L rho, int k) {
    for (int i = 0; i + 6 < NR; i++) {
        int okr = 1; for (int q = 0; q < 7; q++) if (strcmp(SH[i + q], ROUTE[q])) { okr = 0; break; }
        if (!okr) continue;
        L g = SW[i].b - (2 * rho + 6);
        unsigned long long x = ((unsigned long long)SW[i].b - TSTAR) & ((1ULL << 40) - 1);
        int v = 0; while (v < 40 && !((x >> v) & 1)) v++;
        int G = v - 3; if (G < 0) G = 0;
        if (g >= 0 && g < 4000) stagecnt[(int)g][G]++;
        if (G >= 9) { printf("  main route gap %d at class ", G); pr128(rho); printf(" mod 2^%d, growth %d, round %d\n", k, (int)g, i); }
    }
}
typedef struct { L rho; int tc, bc; double h; } C;
static int cmpc(const void *x, const void *y) { const C *a = x, *b = y;
    if (a->bc != b->bc) return b->bc - a->bc; if (a->tc != b->tc) return b->tc - a->tc; if (a->h != b->h) return b->h > a->h ? 1 : -1; return b->bc - a->bc; }
static void pr128(L x) { char buf[64]; int i = 63; buf[i] = 0; if (x == 0) { printf("0"); return; } while (x > 0) { buf[--i] = '0' + (int)(x % 10); x /= 10; } printf("%s", buf + i); }
int main(int argc, char **argv) {
    int K = atoi(argv[1]); int B = atoi(argv[2]);
    { unsigned long long inv = 1; for (int it = 0; it < 7; it++) inv = inv * (2 - 1225ULL * inv); TSTAR = (unsigned long long)(-(long long)38423) * inv; }
    C *beam = malloc(sizeof(C) * (size_t)B * 2 + 16), *cand = malloc(sizeof(C) * (size_t)B * 4 + 16);
    int nb = 1; beam[0] = (C){ 0, 0, 0, 0 };   /* class mod 2^1: n even */
    int k0 = 1;
    int bestsettled = 0;
    for (int k = k0; k < K; k++) {
        int nc = 0; int settled_best = 0; double settled_h = 0; L settled_rho = 0; int halts = 0;
        for (int i = 0; i < nb; i++) for (int bit = 0; bit < 2; bit++) {
            L rho = beam[i].rho + (bit ? ((L)1) << k : 0);
            int s = cycle(k + 1, rho);
            if (s == 2) { halts++; printf("HALT class "); pr128(rho); printf(" mod 2^%d\n", k + 1); continue; }
            if (s == 0) { scan_routes(rho, k + 1); int c = chain_len(); double h = halv(); if (c > settled_best || (c == settled_best && h > settled_h)) { settled_best = c; settled_h = h; settled_rho = rho; } continue; }
            if (s == 1) { scan_routes(rho, k + 1); cand[nc++] = (C){ rho, trailing_chain(), NR, halv() }; }
        }
        qsort(cand, nc, sizeof(C), cmpc);
        nb = nc < B ? nc : B; memcpy(beam, cand, sizeof(C) * nb);
        if (settled_best > bestsettled) bestsettled = settled_best;
        printf("depth %3d: open %6d kept %5d | open best trailing run %2d (h %.1f) | settled best chain %2d h %.1f class ",
               k + 1, nc, nb, nb ? beam[0].tc : 0, nb ? beam[0].h : 0, settled_best, settled_h);
        pr128(settled_rho); printf(" | overall %d\n", bestsettled); fflush(stdout);
        if (nb == 0) break;
    }
    for (int g = 0; g < 4000; g++) { long long t = 0; int mx = 0; for (int G = 0; G < 40; G++) if (stagecnt[g][G]) { t += stagecnt[g][G]; mx = G; }
        if (t) { printf("stage growth %4d: %lld route entries seen, max gap %d :", g, t, mx); for (int G = 0; G < 40; G++) if (stagecnt[g][G]) printf(" %d:%lld", G, stagecnt[g][G]); printf("\n"); } }
    return 0;
}
