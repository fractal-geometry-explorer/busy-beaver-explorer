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
typedef __int128 i128;
static int DEPTH = 4; static int TAUOUT = 0; static char shp[3][16]; static char ring[12][16]; static Q ringM[12], ringW[12]; static i128 pstau_num[64], pstau_den[64]; static int pstau_ok[64]; static ll psgrow[64]; static int psround[64]; static ll CURRHO; static int CURROUND; static int nring; static char pskey[64][200]; static Q gR[3], gL[3]; static int gok[3];
static i128 psR_a[64], psR_b[64], psL_a[64], psL_b[64]; static int nps;
static void shape_now(char *out) {
    int idx[MAXM], k = 0; for (int i = 0; i < nm; i++) if (A[i]) idx[k++] = i;
    for (int i = 1; i < k; i++) { int v = idx[i], j = i - 1; while (j >= 0 && qcmp(P[idx[j]], P[v]) > 0) { idx[j+1] = idx[j]; j--; } idx[j+1] = v; }
    memset(out, 0, 16); for (int i = 0; i < k && i < 15; i++) out[i] = T[idx[i]];
    if (!strcmp(out, "GWWW")) { Q b = P[idx[2]], c = P[idx[3]];
        gR[2] = (Q){ W.a - c.a, W.b - c.b - 1 };
        gL[2] = (Q){ 1029 * b.a + 1960 * W.a - 2744 * c.a, 1029 * b.b + 1960 * W.b - 2744 * c.b - 4046 }; gok[2] = 1; }
    else gok[2] = 0;
}
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
    nps = 0; memset(shp, 0, sizeof shp); gok[0] = gok[1] = gok[2] = 0; nring = 0;
    CURRHO = rho;
    for (int r = 1; r <= 20000; r++) {
        do_round(); CURROUND = r;
        if (need) return 1;
        if (!halted && !bad) {
            memmove(shp[0], shp[1], 32); gR[0] = gR[1]; gR[1] = gR[2]; gL[0] = gL[1]; gL[1] = gL[2]; gok[0] = gok[1]; gok[1] = gok[2];
            shape_now(shp[2]);
            memmove(ring[0], ring[1], 11 * 16); memcpy(ring[11], shp[2], 16); nring++;
            memmove(ringM, ringM + 1, 11 * sizeof(Q)); memmove(ringW, ringW + 1, 11 * sizeof(Q));
            { int idx[MAXM], kk = 0; for (int i = 0; i < nm; i++) if (A[i]) idx[kk++] = i;
              for (int i = 1; i < kk; i++) { int v = idx[i], j = i - 1; while (j >= 0 && qcmp(P[idx[j]], P[v]) > 0) { idx[j+1] = idx[j]; j--; } idx[j+1] = v; }
              ringM[11] = kk > 1 ? P[idx[1]] : (Q){0, 0}; ringW[11] = W; }
            if (gok[0] && !strcmp(shp[1], "GBW") && !strcmp(shp[2], "GMB") && nps < 64) {
                psR_a[nps] = gR[0].a; psR_b[nps] = gR[0].b; psL_a[nps] = gL[0].a; psL_b[nps] = gL[0].b;
                /* key: the DEPTH shapes before the pass start (ring[9] is the GWWW state) */
                char *kp = pskey[nps]; kp[0] = 0;
                for (int t = 9 - DEPTH; t < 9; t++) { if (t < 0 || 11 - t >= nring) { strcat(kp, "- "); continue; } strcat(kp, ring[t]); strcat(kp, " "); }
                /* tau at the state four rounds before the pass start (ring[5]): tau = bE - bM*aE/aM  (2-adic) */
                pstau_ok[nps] = (nring >= 7);
                if (pstau_ok[nps]) { Q mq = ringM[5], wq = ringW[5];
                    pstau_num[nps] = (i128)wq.b * mq.a - (i128)mq.b * wq.a; pstau_den[nps] = mq.a; psgrow[nps] = wq.b - (2 * CURRHO + 6); psround[nps] = CURROUND - 4; }
                nps++; }
        }
        if (halted) return 2;
        if (bad) return 3;
        int alive = 0, ok = 0; Q e = qadd(W, -2);
        for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M' && qcmp(P[i], e) == 0) ok = 1; }
        if (alive == 2 && ok) { *jump = (W.b - (2 * rho + 6)) / 2; *rounds = r; *chain = chain_len(); return 0; }
    }
    return 4;
}
static int v2q(i128 x) { if (!x) return 999; if (x < 0) x = -x; int c = 0; while (!(x & 1)) { x >>= 1; c++; } return c; }
#define HS 1048576
static char hkey[HS][200]; static long long hcnt[HS][40]; static int hused[HS];

static unsigned long hh(const char *k) { unsigned long h = 1469598103934665603UL; while (*k) { h ^= (unsigned char)*k++; h *= 1099511628211UL; } return h; }
static void hadd(const char *k, int g) { unsigned long h = hh(k) & (HS - 1);
    while (hused[h] && strcmp(hkey[h], k)) h = (h + 1) & (HS - 1);
    if (!hused[h]) { hused[h] = 1; strcpy(hkey[h], k); } hcnt[h][g]++; }
static long double gdens[40][40]; static long long gcnt[40][40]; static int gmaxR = 0, gmaxL = 0;
int main(int argc, char **argv) {
    int K = atoi(argv[1]); if (argc > 3) DEPTH = atoi(argv[3]); TAUOUT = getenv("TAUOUT") != NULL; long long cap = argc > 2 ? atoll(argv[2]) : 200000000LL;
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
                if (chain >= 12) printf("  chain %d: n = %lld (mod 2^%d), jump %lld, %d rounds\n", chain, rho, k, jump, rounds);
                for (int q = 0; q < nps; q++) {
                    i128 D = psR_a[q] * psL_b[q] - psL_a[q] * psR_b[q];
                    int GL = v2q(D) - v2q(psR_a[q]), GR = v2q(D) - v2q(psL_a[q]);
                    if (GL < 0) GL = 0; if (GR < 0) GR = 0; if (GL > 39) GL = 39; if (GR > 39) GR = 39;
                    gdens[GL][GR] += 1.0L / (long double)(1ULL << k); gcnt[GL][GR]++; hadd(pskey[q], GR);
                    if (TAUOUT && pstau_ok[q] && !strcmp(pskey[q], "GMM GMMM GMMW GMWW ")) {
                        i128 num = pstau_num[q], den = pstau_den[q]; int e = 0;
                        while (den % 2 == 0 && num % 2 == 0) { den /= 2; num /= 2; }
                        while (den % 2 == 0) { den /= 2; e++; }
                        /* tau = num / (den * 2^e) with den odd; print tau mod 2^24 if e == 0 */
                        if (e == 0) { unsigned long long M = 1ULL << 24; long long dn = (long long)(den % (i128)M); if (dn < 0) dn += M;
                            unsigned long long inv = 1; for (int it = 0; it < 6; it++) inv = inv * (2 - (unsigned long long)dn * inv);
                            long long nn = (long long)(num % (i128)M); if (nn < 0) nn += M;
                            printf("TAU %llu GR %d rho %lld k %d grow %lld round %d\n", ((unsigned long long)nn * inv) % M, GR, rho & 0xFFFF, k, psgrow[q], psround[q]); }
                        else printf("TAU nonint e=%d GR %d\n", e, GR); }
                    if (GR > gmaxR || GL > gmaxL) { if (GR > gmaxR) gmaxR = GR; if (GL > gmaxL) gmaxL = GL;
                        printf("  new largest gap: GL %d GR %d at n = %lld (mod 2^%d), pass start %d of the cycle, chain %d\n", GL, GR, rho, k, q + 1, chain); }
                }
            } else { other++; printf("  class n = %lld (mod 2^%d): %s\n", rho, k, s == 2 ? "HALTS" : s == 3 ? "contact/bad" : "too long"); }
        }
        if (newmax > cummax) cummax = newmax;
        printf("digits %2d: settled %lld, still open %lld, longest chain settled here %d (overall %d); chain counts:", k, settled, nn / 2, newmax, cummax);
        for (int c = 0; c < 64; c++) if (hist[c]) printf(" %d:%lld", c, hist[c]);
        printf("\n"); printf("   largest gaps so far: GL %d, GR %d\n", gmaxL, gmaxR); fflush(stdout);
        free(cur); cur = nx; nc = nn;
        if (nc > cap) { printf("stopping: %lld open classes exceed the cap\n", nc); break; }
    }
    printf("pass starts by gaps (GL, GR): count, density\n");
    for (int a = 0; a < 40; a++) for (int b = 0; b < 40; b++) if (gcnt[a][b]) printf("  (%d, %d): %lld  %.3Le\n", a, b, gcnt[a][b], gdens[a][b]);
    printf("pass starts by the %d round shapes before them: lines with each G_R\n", DEPTH);
    for (int h = 0; h < HS; h++) if (hused[h]) { long long t = 0; int mx = 0; for (int g = 0; g < 40; g++) if (hcnt[h][g]) { t += hcnt[h][g]; mx = g; }
        printf("  route [%s] lines %lld max G_R %d :", hkey[h], t, mx); for (int g = 0; g < 40; g++) if (hcnt[h][g]) printf(" %d:%lld", g, hcnt[h][g]); printf("\n"); }
    printf("density of settled n by chain length:");
    for (int c = 0; c < 64; c++) if (dens[c] > 0) printf(" %d:%.3Le", c, dens[c]);
    printf("\n");
    return 0;
}
