/* gx: exhaustive 2-adic exploration of the mark model from a state whose positions are free variables.
   Positions are affine forms (sum c_i x_i + c_NV) / 2^e in the variables x_0 < x_1 < ... < x_{nv-1} (the last is the
   tape end E). Order comparisons are decided on the cone 0 < x_0 < ... < x_{nv-1} (large separations); a comparison
   that the cone does not decide falls back to a virtual point and is counted. Each d (mod 4) test is either fixed on
   the current coset of allowed integer points or splits it in half (one bit). The coset is kept in Hermite form.

   Modes:
     gx exit K CAP X0 ... X_{nv-1}         loop with K extra walls: state G W^(3+K), end; one pass or the exit
     gx run CAP SHAPE X1 ... Xm XE         a run-start state (marks after G, then the end); follow the run that starts
                                           in the first round until it reaches a loop state or ends
     gx closure CAP                        closure of run-start states from the clean tape and the loop state
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
typedef __int128 i128;
typedef long long ll;
#define NV 14
#define MAXM 24
static int nv;                       /* number of variables in use; variable nv-1 is the end E */
static long double X[NV];            /* virtual point */
static long long geodep = 0, ncmp = 0;

typedef struct { i128 c[NV + 1]; int e; } Form;     /* c[NV] is the constant */

static void fnorm(Form *f) {
    while (f->e > 0) {
        int ok = 1; for (int i = 0; i <= NV; i++) if (f->c[i] & 1) { ok = 0; break; }
        if (!ok) break;
        for (int i = 0; i <= NV; i++) f->c[i] >>= 1;
        f->e--;
    }
}
static Form fconst(ll k) { Form f; memset(&f, 0, sizeof f); f.c[NV] = k; return f; }
static Form fvar(int i) { Form f; memset(&f, 0, sizeof f); f.c[i] = 1; return f; }
static Form fadd(Form a, Form b, int sign) {
    Form r; memset(&r, 0, sizeof r);
    int E = a.e > b.e ? a.e : b.e;
    for (int i = 0; i <= NV; i++) r.c[i] = (a.c[i] << (E - a.e)) + sign * (b.c[i] << (E - b.e));
    r.e = E; fnorm(&r); return r;
}
static Form faddc(Form a, ll k) { a.c[NV] += ((i128)k) << a.e; fnorm(&a); return a; }
static Form fhalf(Form a) { a.e++; fnorm(&a); return a; }
static int feq(Form a, Form b) { if (a.e != b.e) return 0; for (int i = 0; i <= NV; i++) if (a.c[i] != b.c[i]) return 0; return 1; }
static int fisconst(Form a, ll k) { for (int i = 0; i < NV; i++) if (a.c[i]) return 0; return a.e == 0 && a.c[NV] == k; }
static long double fval(Form a) {
    long double v = (long double)a.c[NV];
    for (int i = 0; i < nv; i++) v += (long double)a.c[i] * X[i];
    return ldexpl(v, -a.e);
}
/* sign of a - b on the cone */
static int fcmp(Form a, Form b) {
    ncmp++;
    Form d = fadd(a, b, -1);
    int pos = 0, neg = 0; i128 beta = 0;
    for (int k = nv - 1; k >= 0; k--) { beta += d.c[k]; if (beta > 0) pos = 1; else if (beta < 0) neg = 1; }
    if (!pos && !neg) return d.c[NV] > 0 ? 1 : d.c[NV] < 0 ? -1 : 0;
    if (pos && !neg) return 1;
    if (neg && !pos) return -1;
    geodep++;
    long double v = fval(d); return v > 0 ? 1 : v < 0 ? -1 : 0;
}

/* ---- coset x = x0 + B y ---- */
typedef struct { i128 x0[NV]; i128 B[NV][NV]; int bits; } Coset;
static i128 iabs(i128 a) { return a < 0 ? -a : a; }
static i128 fdiv(i128 a, i128 b) { i128 q = a / b; if ((a % b != 0) && ((a < 0) != (b < 0))) q--; return q; }
static void hnf(Coset *C) {
    for (int r = 0; r < nv; r++) {
        for (int c = r + 1; c < nv; c++) {
            while (C->B[r][c] != 0) {
                if (C->B[r][r] == 0 || iabs(C->B[r][c]) < iabs(C->B[r][r])) {
                    for (int i = 0; i < nv; i++) { i128 t = C->B[i][r]; C->B[i][r] = C->B[i][c]; C->B[i][c] = t; }
                    continue;
                }
                i128 q = C->B[r][c] / C->B[r][r];
                for (int i = 0; i < nv; i++) C->B[i][c] -= q * C->B[i][r];
            }
        }
        if (C->B[r][r] < 0) for (int i = 0; i < nv; i++) C->B[i][r] = -C->B[i][r];
        for (int c = 0; c < r; c++) {
            i128 q = fdiv(C->B[r][c], C->B[r][r]);
            if (q) for (int i = 0; i < nv; i++) C->B[i][c] -= q * C->B[i][r];
        }
    }
    for (int r = 0; r < nv; r++) {
        i128 q = fdiv(C->x0[r], C->B[r][r]);
        if (q) for (int i = 0; i < nv; i++) C->x0[i] -= q * C->B[i][r];
    }
}
/* f0 and g on the coset; returns 0 if not integral / not even (invalid path) */
static int evalf(const Coset *C, Form f, i128 *f0, i128 *g) {
    i128 num = f.c[NV];
    for (int i = 0; i < nv; i++) num += f.c[i] * C->x0[i];
    i128 mask = (((i128)1) << f.e) - 1;
    if (num & mask) return 0;
    *f0 = num >> f.e;
    for (int k = 0; k < nv; k++) {
        i128 s = 0; for (int i = 0; i < nv; i++) s += f.c[i] * C->B[i][k];
        if (s & mask) return 0;
        g[k] = s >> f.e;
    }
    if (*f0 & 1) return 0;
    for (int k = 0; k < nv; k++) if (g[k] & 1) return 0;
    return 1;
}
/* -1 undecided, -2 invalid, else 0 or 2 */
static int decided(const Coset *C, Form f) {
    i128 f0, g[NV]; if (!evalf(C, f, &f0, g)) return -2;
    for (int k = 0; k < nv; k++) if ((g[k] >> 1) & 1) return -1;
    return (int)(((f0 % 4) + 4) % 4);
}
static void impose(Coset *C, Form f, int res) {
    i128 f0, g[NV]; evalf(C, f, &f0, g);
    i128 h[NV]; for (int k = 0; k < nv; k++) h[k] = g[k] >> 1;
    int t = (int)((((res - f0) >> 1) % 2 + 2) % 2);
    int i = -1; for (int k = 0; k < nv; k++) if (h[k] & 1) { i = k; break; }
    for (int r = 0; r < nv; r++) C->x0[r] += t * C->B[r][i];
    for (int k = 0; k < nv; k++) if (k != i) for (int r = 0; r < nv; r++) C->B[r][k] -= h[k] * C->B[r][i];
    for (int r = 0; r < nv; r++) C->B[r][i] *= 2;
    C->bits++;
    hnf(C);
}

/* ---- model ---- */
typedef struct {
    char T[MAXM]; Form P[MAXM]; char A[MAXM]; int nm; Form W; int halted, bad;
    int nmeet; Form md[8]; char mres[8]; char mlast[8];      /* meetings in the current round */
} State;
static unsigned char *OLOG; static int *NO; static short *OROUND; static int CURRD;
static State S; static Coset *CO; static int *FORCED, NFORCED, FI, NEEDBR;
static int add(char t, Form p) { for (int i = 0; i < S.nm; i++) if (!S.A[i]) { S.T[i] = t; S.P[i] = p; S.A[i] = 1; return i; }
    if (S.nm >= MAXM) { S.bad = 9; return 0; } S.T[S.nm] = t; S.P[S.nm] = p; S.A[S.nm] = 1; return S.nm++; }
static int first_right(Form x) { int b = -1; for (int i = 0; i < S.nm; i++) if (S.A[i] && fcmp(S.P[i], x) > 0 && (b < 0 || fcmp(S.P[i], S.P[b]) < 0)) b = i; return b; }
static int last_mark(void) { int b = -1; for (int i = 0; i < S.nm; i++) if (S.A[i] && (b < 0 || fcmp(S.P[i], S.P[b]) > 0)) b = i; return b; }
static int packet_back(Form x) {
    int b = -1; for (int i = 0; i < S.nm; i++) if (S.A[i] && S.T[i] != 'M' && fcmp(S.P[i], x) < 0 && (b < 0 || fcmp(S.P[i], S.P[b]) > 0)) b = i;
    if (b < 0) return -1;
    if (S.T[b] == 'B') { S.halted = 1; return -1; }
    if (S.T[b] == 'G') { S.P[b] = faddc(S.P[b], 2); return b; }
    Form q = S.P[b]; S.T[b] = 'M'; S.P[b] = faddc(q, -1); return add('G', faddc(q, 1));
}
static int shift_from(Form x) {
    int k = first_right(x);
    if (k < 0) { S.W = faddc(S.W, 2); add('M', faddc(S.W, -2)); return packet_back(faddc(S.W, -2)); }
    if (S.T[k] == 'M') { S.T[k] = 'G'; return k; }
    if (S.T[k] == 'W') { S.T[k] = 'B'; return packet_back(S.P[k]); }
    if (S.T[k] == 'B') { S.T[k] = 'W'; S.P[k] = faddc(S.P[k], 2); return packet_back(S.P[k]); }
    S.bad = 2; return -1;
}
static int DBGROUND = 0;
static int test_(Form d);
static int test(Form d) { int r = test_(d); if (r >= 0 && OLOG && *NO < 400) { OROUND[*NO] = CURRD; OLOG[(*NO)++] = r; } return r; }
static int test_(Form d) {
    int r = decided(CO, d);
    if (getenv("GXDEBUG3") && DBGROUND) { printf("  test e=%d c:", d.e); for (int i = 0; i < nv; i++) printf(" %lld", (ll)d.c[i]); printf(" const %lld -> %d (bits %d)\n", (ll)d.c[NV], r, CO->bits); }
    if (r == -2) {
        if (getenv("GXDEBUG2")) { printf("invalid form e=%d c:", d.e); for (int i = 0; i < nv; i++) printf(" %lld", (ll)d.c[i]); printf(" const %lld | x0:", (ll)d.c[NV]); for (int i = 0; i < nv; i++) printf(" %lld", (ll)CO->x0[i]); printf(" | diag:"); for (int i = 0; i < nv; i++) printf(" %lld", (ll)CO->B[i][i]); printf("\n"); }
        S.bad = 3; return -1; }
    if (r >= 0) return r;
    if (FI < NFORCED) { int v = FORCED[FI++]; impose(CO, d, v); return v; }
    NEEDBR = 1; return -1;
}
static void do_round(void) {
    S.nmeet = 0;
    int gap = -1; for (int i = 0; i < S.nm; i++) if (S.A[i] && S.T[i] == 'G' && fisconst(S.P[i], 1)) gap = i;
    while (gap >= 0 && !S.halted && !S.bad) {
        Form g = S.P[gap]; int m = first_right(g);
        if (m < 0) { S.A[gap] = 0; S.W = faddc(S.W, 3); add('M', faddc(S.W, -2)); gap = packet_back(faddc(S.W, -2)); continue; }
        if (S.T[m] == 'M') {
            Form d = faddc(fadd(S.P[m], g, -1), -3);
            if (fcmp(d, fconst(0)) < 0) { S.bad = 5; return; }
            int last = (m == last_mark());
            int res = test(d); if (NEEDBR || S.bad) return;
            if (last && S.nmeet < 8) { S.md[S.nmeet] = d; S.mres[S.nmeet] = res; S.mlast[S.nmeet] = 1; S.nmeet++; }
            Form h = fhalf(d);
            if (res == 0) { S.P[m] = faddc(fadd(g, h, 1), -1); S.P[gap] = faddc(fadd(g, h, 1), 1); }
            else { S.A[gap] = 0; S.T[m] = 'W'; S.P[m] = faddc(fadd(g, h, 1), 3); gap = packet_back(S.P[m]); }
        } else if (S.T[m] == 'W') { Form x = S.P[m]; S.A[gap] = 0; S.A[m] = 0; gap = shift_from(x); }
        else if (S.T[m] == 'B') { S.T[m] = 'W'; S.P[m] = faddc(S.P[m], -1); gap = shift_from(S.P[m]); }
        else { S.bad = 4; return; }
    }
    if (S.halted || S.bad) return;
    ll extra = 2;
    for (int i = 0; i < S.nm; i++) if (S.A[i] && S.T[i] == 'M' && fisconst(S.P[i], 0)) { S.T[i] = 'W'; S.P[i] = fconst(1); extra = 4; }
    for (int i = 0; i < S.nm; i++) if (S.A[i]) S.P[i] = faddc(S.P[i], extra);
    S.W = faddc(S.W, extra); add('G', fconst(1));
}
static void shape(const State *st, char *out, int *idx_out, int *kout) {
    int idx[MAXM], k = 0; for (int i = 0; i < st->nm; i++) if (st->A[i]) idx[k++] = i;
    for (int i = 1; i < k; i++) { int v = idx[i], j = i - 1; while (j >= 0 && fcmp(st->P[idx[j]], st->P[v]) > 0) { idx[j+1] = idx[j]; j--; } idx[j+1] = v; }
    memset(out, 0, 16); for (int i = 0; i < k && i < 15; i++) out[i] = st->T[idx[i]];
    if (idx_out) memcpy(idx_out, idx, sizeof(int) * k);
    if (kout) *kout = k;
}
static int is_clean(const State *st) {
    int alive = 0, ok = 0; Form e = faddc(st->W, -2);
    for (int i = 0; i < st->nm; i++) if (st->A[i]) { alive++; if (st->T[i] == 'M' && feq(st->P[i], e)) ok = 1; }
    return alive == 2 && ok;
}
static Form pred(Form d, int res) { return res == 2 ? fhalf(faddc(d, -2)) : faddc(fhalf(d), 4); }

/* ---- DFS ---- */
#define HMAX 160
typedef struct {
    State st; Coset co; int forced[48]; int nf; int rounds;
    char hist[HMAX][16]; int nh; float lL[HMAX], lR[HMAX];
    int runlen; Form rlast; int rres; int started;
    int runstart; int maxrun; int maxst; int kinds;
    unsigned char olog[400]; int no; short oround[400];
    int xm, hasg; Form gb, gc, gW;
} Item;
static Item *stack_; static long long sp, scap;
static void push(const Item *it) {
    if (sp >= scap) { scap = scap ? scap * 2 : 1024; stack_ = realloc(stack_, sizeof(Item) * scap); if (!stack_) { fprintf(stderr, "out of memory\n"); exit(1); } }
    stack_[sp++] = *it;
}
static const ll LC[5][9] = {{0, 147, -245, 168, -491}, {0, 441, -735, 2156, -1652, 179}, {0, 1323, -2205, 6468, -22148, 17192, -16655},
    {0, 3969, -6615, 19404, -66444, 229124, -177548, 127583}, {0, 11907, -19845, 58212, -199332, 687372, -2355332, 1822688, -1439939}};
static void sizes(const State *st, const char *sh, float *lL, float *lR) {
    *lL = *lR = -99;
    if (strncmp(sh, "GWWW", 4)) return;
    for (const char *p = sh + 4; *p; p++) if (*p != 'W') return;
    int k = (int)strlen(sh) - 4; if (k > 4) return;
    int idx[MAXM], n; char tmp[16]; shape(st, tmp, idx, &n);
    long double L = 0, E = fval(st->W);
    for (int q = 1; q < n; q++) L += (long double)LC[k][q - 1] * fval(st->P[idx[q]]);
    L += (long double)LC[k][n - 1] * E + (long double)LC[k][n];
    long double R = E - fval(st->P[idx[n - 1]]) - 1;
    *lL = (float)(log2l(fabsl(L)) - log2l(E)); *lR = (float)(log2l(R) - log2l(E));
}
static const char *LOOP[8] = {"GWWW", "GBW", "GMB", "GMWW", "GMB", "GMWW", "GWWW", "GBW"};
static void loopshape(int k, int ph, char *out) { strcpy(out, LOOP[ph % 8]); for (int i = 0; i < k; i++) strcat(out, "W"); }
static int is_loop_state(const char *sh) { if (strncmp(sh, "GWWW", 4)) return -1; for (const char *p = sh + 4; *p; p++) if (*p != 'W') return -1; return (int)strlen(sh) - 4; }
/* does hist[from..] contain >= 4 consecutive rounds of the loop with some k' (0..6)? returns k' or -1 */
static int later_loop(Item *it, int from) {
    char s[16];
    for (int kk = 0; kk <= 6; kk++) for (int i = from; i < it->nh; i++) for (int ph = 0; ph < 8; ph++) {
        int j = 0; while (i + j < it->nh) { loopshape(kk, ph + j, s); if (strcmp(it->hist[i + j], s)) break; j++; }
        if (j >= 4) return kk;
    }
    return -1;
}

static int count_stretches(Item *it, int *kinds) {
    char sh[16]; int n = 0, i = 0; *kinds = 0;
    while (i < it->nh) {
        int best = 0, bk = -1;
        for (int kk = 0; kk <= 6; kk++) for (int ph = 0; ph < 8; ph++) {
            int j = 0; while (i + j < it->nh) { loopshape(kk, ph + j, sh); if (strcmp(it->hist[i + j], sh)) break; j++; }
            if (j > best) { best = j; bk = kk; }
        }
        if (best >= 4) { n++; *kinds |= 1 << bk; i += best; } else i++;
    }
    return n;
}
static long double runmass[64], runmass1[64];
static int stretches_range(Item *it, int a, int b, int *kinds) {
    char sh[16]; int n = 0, i = a; *kinds = 0;
    while (i < b && i < it->nh) {
        int best = 0, bk = -1;
        for (int kk = 0; kk <= 6; kk++) for (int ph = 0; ph < 8; ph++) {
            int j = 0; while (i + j < b && i + j < it->nh) { loopshape(kk, ph + j, sh); if (strcmp(it->hist[i + j], sh)) break; j++; }
            if (j > best) { best = j; bk = kk; }
        }
        if (best >= 4) { n++; *kinds |= 1 << bk; i += best; } else i++;
    }
    return n;
}
static long double linemass[64]; static long long linest[8]; static long double linestm[8]; static int lineshown;
static void finish_run(Item *nx, int endidx) {
    int kinds; int ns = stretches_range(nx, nx->runstart, endidx, &kinds);
    if (nx->runlen > nx->maxrun) nx->maxrun = nx->runlen;
    if (ns > nx->maxst) nx->maxst = ns;
    nx->kinds |= kinds;
} static int nshown_ = 0; static long long chainhist[16]; static long double chainmass[16]; static int NOSTOP = 0;
/* results */
static long long nbad = 0; static long double p_pass = 0; static long long n_exit = 0, n_cut = 0, n_halt = 0, n_toloop = 0;
static int max_exit_run = 0, max_toloop_run = 0; static long long later[8];
static long long exit_hist[64];
#define NNEW 256
static char newsh[NNEW][16]; static long double newgeo[NNEW][MAXM + 1]; static int newnpos[NNEW]; static char newtie[NNEW][MAXM]; static int nnew;

static void record_new(const State *st) {
    char sh[16]; int idx[MAXM], k; shape(st, sh, idx, &k);
    for (int i = 0; i < nnew; i++) if (!strcmp(newsh[i], sh)) return;
    if (nnew >= NNEW) return;
    strcpy(newsh[nnew], sh); newnpos[nnew] = k - 1;
    /* tie: 'E' = same variable part as the end, 'C' = constant, 'P' = same variable part as the previous mark */
    for (int q = 1; q < k; q++) {
        Form f = st->P[idx[q]]; int isc = 1; for (int i = 0; i < NV; i++) if (f.c[i]) isc = 0;
        Form dE = fadd(f, st->W, -1); int tieE = 1; for (int i = 0; i < NV; i++) if (dE.c[i]) tieE = 0;
        int tieP = 0; if (q > 1) { Form dP = fadd(f, st->P[idx[q - 1]], -1); tieP = 1; for (int i = 0; i < NV; i++) if (dP.c[i]) tieP = 0; }
        newtie[nnew][q - 1] = isc ? 'C' : tieE ? 'E' : tieP ? 'P' : 'F';
        newgeo[nnew][q - 1] = fval(f);
        if (isc || tieE || tieP) newgeo[nnew][q - 1] = (long double)(isc ? fval(f) : tieE ? (fval(f) - fval(st->W)) : (fval(f) - fval(st->P[idx[q - 1]])));
    }
    newgeo[nnew][k - 1] = fval(st->W);
    nnew++;
}


/* ---- xlead: plain entries reached from an extra-wall state ---- */
static int MMAX = 2; static long long n_more = 0, n_entry = 0; static int PLAT = 0;
#define SB 96
static long double emass[8][SB]; static long long ecount[8][SB]; static long double emax[8]; static long double emass_tot[8];
typedef struct { long double sig, s, lam; int bits; char word[600]; double beta[NV]; double b0; Coset co; } Top;
static Top tops[8][4]; static int ntops[8]; static long double jmass[64], jlam[64]; static long double S2;
static void record_entry(Item *it) {
    Form R1 = faddc(fadd(it->gW, it->gc, -1), -1);
    Form t1 = it->gb; for (int i = 0; i <= NV; i++) t1.c[i] *= 147;
    Form t2 = it->gW; for (int i = 0; i <= NV; i++) t2.c[i] *= 280;
    Form t3 = it->gc; for (int i = 0; i <= NV; i++) t3.c[i] *= 392;
    Form L1 = faddc(fadd(fadd(t1, t2, 1), t3, -1), -578);
    long double W = fval(it->gW), Rv = fval(R1), Lv = fval(L1);
    if (Rv <= 0) return;
    long double s_ = log2l(W / Rv), lam = log2l(fabsl(Lv) / W), sig = 3 * s_ + 2 * lam;
    int m = it->xm < 7 ? it->xm : 7; long double w = ldexpl(1.0L, -it->co.bits);
    int b = (int)floorl(sig); if (b < 0) b = 0; if (b >= SB) b = SB - 1;
    emass[m][b] += w; ecount[m][b]++; emass_tot[m] += w; n_entry++;
    if (getenv("GXENTRIES")) { printf("E sigma %.3Lf s %.3Lf lambda %.3Lf bits %d m %d |", sig, s_, lam, it->co.bits, it->xm); for (int q = 0; q < it->nh; q++) printf(" %s", it->hist[q]); printf("\n"); }
    if (sig > emax[m]) emax[m] = sig;
    { int j = (int)llroundl(s_ - S2); if (j < 0) j = 0; if (j > 63) j = 63; jmass[j] += w; if (lam > jlam[j]) jlam[j] = lam; }
    /* keep the 4 largest sigma per m */
    int pos = ntops[m] < 4 ? ntops[m]++ : 3;
    if (pos == 3 && ntops[m] == 4 && tops[m][3].sig >= sig) return;
    Top t; t.sig = sig; t.s = s_; t.lam = lam; t.bits = it->co.bits; t.word[0] = 0;
    for (int q = 0; q < it->nh && strlen(t.word) < 560; q++) { strcat(t.word, it->hist[q]); strcat(t.word, " "); }
    for (int j = 0; j < nv; j++) { long double acc = 0; for (int k = j; k < nv; k++) acc += (long double)R1.c[k]; t.beta[j] = (double)ldexpl(acc, -R1.e); }
    t.b0 = (double)ldexpl((long double)R1.c[NV], -R1.e); t.co = it->co;
    tops[m][pos] = t;
    for (int i = pos; i > 0 && tops[m][i].sig > tops[m][i - 1].sig; i--) { Top x = tops[m][i]; tops[m][i] = tops[m][i - 1]; tops[m][i - 1] = x; }
}
static const char *PW[8] = {"GBWW", "GWWWW", "GBWW", "GMBW", "GMWWW", "GMBW", "GMWWW", "GWWWW"};
static const char *QW[8] = {"GBWW", "GMMWW", "GMWWW", "GMBW", "GMWWW", "GMBW", "GMWWW", "GWWWW"};
static int is_word(Item *it, const char **w) { for (int q = 0; q < 8; q++) if (strcmp(it->hist[it->nh - 8 + q], w[q])) return 0; return 1; }


/* ---- endgame: from a phase-0 pass start G W W W with the end distance R fixed, every branch until the run closes
   (an end meeting at d <= 2), breaks far from the end, starts a new phase-0 pass, or is not in phase 0 ---- */
static int MODE, KX, CAP;
static int isconst(Form f) { for (int i = 0; i < nv; i++) if (f.c[i]) return 0; return 1; }
static long double em_close, em_break, em_pass, em_np0, em_bad, em_halt, em_cut, em_limit;
static long long ec_close, ec_break, ec_pass, ec_np0, ec_bad, ec_halt, ec_cut, ec_limit; static int em_maxmeet, em_maxmeet_close; static int NOPHASE;

static void leaf(const char *kind, int R, Item *it, Coset *co, long long dval) {
    if (!getenv("GXCERT")) return;
    printf("L R=%d %s bits=%d d=%lld x0=%lld,%lld,%lld B=%lld,%lld,%lld,%lld,%lld,%lld rounds=%d |", R, kind, co->bits, dval,
           (ll)co->x0[0], (ll)co->x0[1], (ll)co->x0[2], (ll)co->B[0][0], (ll)co->B[1][0], (ll)co->B[1][1], (ll)co->B[2][0], (ll)co->B[2][1], (ll)co->B[2][2], it->nh - 1);
    for (int q = 1; q < it->nh; q++) printf(" %s", it->hist[q]); printf("\n");
}
static void explore_end(Item *root, int R) {
    sp = 0; push(root);
    while (sp > 0) {
        Item it = stack_[--sp];
        static Coset work; work = it.co;
        OLOG = NULL; NO = NULL; OROUND = NULL;
        S = it.st; CO = &work; FORCED = it.forced; NFORCED = it.nf; FI = 0; NEEDBR = 0; DBGROUND = 0;
        do_round();
        long double w = ldexpl(1.0L, -work.bits);
        if (NEEDBR) {
            if (it.co.bits + it.nf + 1 > CAP) { ec_cut++; em_cut += ldexpl(1.0L, -(it.co.bits + it.nf)); continue; }
            Item a = it; a.forced[a.nf++] = 0; push(&a);
            Item b = it; b.forced[b.nf++] = 2; push(&b);
            continue;
        }
        Item nx = it; nx.st = S; nx.co = work; nx.nf = 0; nx.rounds++;
        char sh[16]; if (!S.bad) shape(&S, sh, NULL, NULL); else strcpy(sh, "(bad)");
        if (nx.nh < HMAX) strcpy(nx.hist[nx.nh++], sh);
        int stop = 0;
        for (int q = 0; q < S.nmeet && !stop; q++) {
            Form d = S.md[q];
            if (nx.started && !feq(pred(nx.rlast, nx.rres), d) && !isconst(d)) { stop = 1; break; }
            nx.started = 1; nx.rlast = d; nx.rres = S.mres[q]; nx.runlen++;
            if (isconst(d) && d.e == 0 && d.c[NV] <= 2) stop = 2;
        }
        if (nx.runlen > em_maxmeet && stop != 2) em_maxmeet = nx.runlen;
        if (stop == 1 && !S.bad) { ec_break++; em_break += w; leaf("break", R, &nx, &work, (ll)-1); continue; }
        if (stop == 2) {
            ec_close++; em_close += w; if (nx.runlen > em_maxmeet_close) em_maxmeet_close = nx.runlen; leaf("close", R, &nx, &work, (ll)nx.rlast.c[NV]);
            printf("C R=%d bits=%d d=%lld x0=%lld,%lld,%lld B=%lld,%lld,%lld,%lld,%lld,%lld |", R, work.bits, (ll)nx.rlast.c[NV],
                   (ll)work.x0[0], (ll)work.x0[1], (ll)work.x0[2], (ll)work.B[0][0], (ll)work.B[1][0], (ll)work.B[1][1], (ll)work.B[2][0], (ll)work.B[2][1], (ll)work.B[2][2]);
            for (int q = 1; q < nx.nh; q++) printf(" %s", nx.hist[q]); printf("\n");
            continue;
        }
        if (S.bad) { ec_bad++; em_bad += w; continue; }
        if (S.halted) { ec_halt++; em_halt += w; continue; }
        if (!NOPHASE && ((nx.rounds == 1 && strcmp(sh, "GBW")) || (nx.rounds == 2 && strcmp(sh, "GMB")))) { ec_np0++; em_np0 += w; leaf("notphase0", R, &nx, &work, (ll)-1); continue; }
        int h = nx.nh;
        if (h >= 4 && !strcmp(nx.hist[h - 3], "GWWW") && !strcmp(nx.hist[h - 2], "GBW") && !strcmp(nx.hist[h - 1], "GMB")) { ec_pass++; em_pass += w; leaf("pass", R, &nx, &work, (ll)-1); continue; }
        if (h >= HMAX - 1) { ec_limit++; em_limit += w; continue; }
        push(&nx);
    }
}


static int CUR_PM = 0;
static void leaf4(const char *kind, Item *it, Coset *co, int runlen, int broken, int fin) {
    if (!getenv("GXCERT")) return;
    printf("X pm=%d %s bits=%d run=%d broken=%d fin=%d x0=", CUR_PM, kind, co->bits, runlen, broken, fin);
    for (int r = 0; r < nv; r++) printf("%s%lld", r ? "," : "", (ll)co->x0[r]);
    printf(" B=");
    int first = 1; for (int r = 0; r < nv; r++) for (int c = 0; c <= r; c++) { printf("%s%lld", first ? "" : ",", (ll)co->B[r][c]); first = 0; }
    printf(" rounds=%d |", it->nh - 1);
    for (int q = 1; q < it->nh; q++) printf(" %s", it->hist[q]); printf("\n");
}

/* mode: 0 exit(K), 1 run-start, 3 xlead, 4 endgame */
static void explore(Item *root) {
    sp = 0;
    if (getenv("GXTRACE")) {   /* follow a single path with forced outcomes for undecided tests, printing everything */
        Item it = *root; const char *fs = getenv("GXTRACE"); int fl[64], nfl = 0; for (const char *p = fs; *p; p++) if (*p == '0' || *p == '2') fl[nfl++] = *p - '0';
        int used = 0;
        for (int r = 0; r < 8; r++) {
            S = it.st; CO = &it.co; FORCED = fl + used; NFORCED = nfl - used; FI = 0; NEEDBR = 0; DBGROUND = 1;
            do_round(); used += FI;
            if (NEEDBR) { printf("needs more outcomes\n"); return; }
            if (S.bad) { printf("bad %d\n", S.bad); return; }
            it.st = S; char sh[16]; shape(&S, sh, NULL, NULL); printf("round %d -> %s (bits %d)\n", r + 1, sh, it.co.bits);
        }
        return;
    }
    push(root);
    while (sp > 0) {
        Item it = stack_[--sp];
        static Coset work; work = it.co;
        static unsigned char olog_w[400]; static short oround_w[400]; static int no_w; memcpy(olog_w, it.olog, it.no); memcpy(oround_w, it.oround, sizeof(short) * it.no); no_w = it.no;
        OLOG = olog_w; OROUND = oround_w; NO = &no_w; CURRD = it.nh;
        S = it.st; CO = &work; FORCED = it.forced; NFORCED = it.nf; FI = 0; NEEDBR = 0; DBGROUND = (it.nh <= 3) && getenv("GXDEBUG3");
        do_round();
        if (NEEDBR) {
            if (it.co.bits + it.nf + 1 > CAP) { n_cut++; continue; }
            Item a = it; a.forced[a.nf++] = 0; push(&a);
            Item b = it; b.forced[b.nf++] = 2; push(&b);
            continue;
        }
        if (S.bad) { if (getenv("GXDEBUG") && nbad < 6) { printf("   bad %d after:", S.bad); for (int q = 0; q < it.nh; q++) printf(" %s", it.hist[q]); printf(" bits %d\n", it.co.bits); } nbad++; continue; }
        if (S.halted) { n_halt++; continue; }
        Item nx = it; nx.st = S; nx.co = work; nx.nf = 0; nx.rounds++; memcpy(nx.olog, olog_w, no_w); memcpy(nx.oround, oround_w, sizeof(short) * no_w); nx.no = no_w;
        char sh[16]; shape(&S, sh, NULL, NULL);
        if (nx.nh < HMAX) { sizes(&S, sh, &nx.lL[nx.nh], &nx.lR[nx.nh]); strcpy(nx.hist[nx.nh++], sh); }
        int broken = 0;
        for (int q = 0; q < S.nmeet; q++) {
            if (nx.started && !feq(pred(nx.rlast, nx.rres), S.md[q])) {
                if (MODE == 2) { finish_run(&nx, nx.nh - 1); nx.runlen = 0; nx.runstart = nx.nh - 1; }
                else if (MODE == 1 && nx.rounds == 1) { nx.runlen = 0; }
                else { broken = 1; break; }
            }
            if (!nx.started || nx.runlen == 0) nx.runstart = nx.nh - 1;
            nx.started = 1; nx.runlen++; nx.rlast = S.md[q]; nx.rres = S.mres[q];
        }
        int fin = is_clean(&S);
        if (MODE == 2) {
            if (fin || nx.nh >= HMAX) {
                finish_run(&nx, nx.nh);
                long double w = ldexpl(1.0L, -nx.co.bits);
                linemass[nx.maxrun < 63 ? nx.maxrun : 63] += w; linest[nx.maxst < 7 ? nx.maxst : 7]++; linestm[nx.maxst < 7 ? nx.maxst : 7] += w;
                if (nx.maxrun > max_exit_run) max_exit_run = nx.maxrun;
                if ((nx.maxst >= 2 || (nx.kinds & ~1)) && lineshown < 5 && getenv("GXPATH")) { lineshown++; printf("   path: longest run %d, most stretches %d, kinds %x, bits %d\n", nx.maxrun, nx.maxst, nx.kinds, nx.co.bits); }
                n_exit++; continue;
            }
            push(&nx); continue;
        }
        if (MODE == 3) {
            if ((broken && !(PLAT && getenv("GXNOBREAK"))) || fin || nx.nh >= HMAX) { n_exit++; continue; }
            if (!strcmp(sh, "GWWW")) { int idx[MAXM], kk; char tmp[16]; shape(&S, tmp, idx, &kk); nx.gb = S.P[idx[2]]; nx.gc = S.P[idx[3]]; nx.gW = S.W; nx.hasg = 1; }
            int h = nx.nh;
            if (h >= 4 && nx.hasg && !strcmp(nx.hist[h - 3], "GWWW") && !strcmp(nx.hist[h - 2], "GBW") && !strcmp(nx.hist[h - 1], "GMB")) { record_entry(&nx); continue; }
            if (h >= 9 && !strcmp(nx.hist[h - 9], "GWWWW") && (is_word(&nx, PW) || is_word(&nx, QW))) { nx.xm++; if (nx.xm > MMAX) { n_more++; continue; } }
            push(&nx); continue;
        }
        if (MODE == 0) {
            if (nx.nh == 9 && !broken && !NOSTOP) {
                int okp = 0; char s[16];
                for (int ph = 0; ph < 8; ph += 6) { int all = 1; for (int q = 0; q < 9; q++) { loopshape(KX, ph + q, s); if (strcmp(nx.hist[q], s)) { all = 0; break; } } if (all) okp = 1; }
                if (okp) { p_pass += ldexpl(1.0L, -nx.co.bits); leaf4("pass", &nx, &nx.co, nx.runlen, 0, 0); continue; }
            }
            if (broken || fin || nx.nh >= HMAX) {
                if (getenv("GXDEBUG") && (n_exit < 12 || getenv("GXALL"))) { printf("   exit run %d bits %d broken %d fin %d:", nx.runlen, nx.co.bits, broken, fin); for (int q = 0; q < nx.nh; q++) printf(" %s", nx.hist[q]); printf("\n"); }
                n_exit++; if (nx.runlen > max_exit_run) max_exit_run = nx.runlen; exit_hist[nx.runlen < 63 ? nx.runlen : 63]++; runmass[nx.runlen < 63 ? nx.runlen : 63] += ldexpl(1.0L, -nx.co.bits); leaf4("exit", &nx, &nx.co, nx.runlen, broken, fin);
                /* rounds following the k-loop from the start */
                int pre = 0; char s[16];
                for (int ph = 0; ph < 8; ph += 6) { int q = 0; while (q < nx.nh) { loopshape(KX, ph + q, s); if (strcmp(nx.hist[q], s)) break; q++; } if (q > pre) pre = q; }
                int kk = later_loop(&nx, pre); if (kk >= 0) later[kk]++;
                { int kinds; int ns = count_stretches(&nx, &kinds); if (!(kinds & 1)) runmass1[nx.runlen < 63 ? nx.runlen : 63] += ldexpl(1.0L, -nx.co.bits); if (ns > 15) ns = 15; chainhist[ns]++; chainmass[ns] += ldexpl(1.0L, -nx.co.bits);
                  if (getenv("GXCHAIN") && ns >= atoi(getenv("GXCHAIN")) && (!getenv("GXKINDS") || kinds == atoi(getenv("GXKINDS"))) && (nshown_ < 2)) { nshown_++; printf("   %d stretches (kinds %x) run %d bits %d:", ns, kinds, nx.runlen, nx.co.bits); for (int q = 0; q < nx.nh; q++) { printf(" %s(", nx.hist[q]); for (int u = 0; u < nx.no; u++) if (nx.oround[u] == q) printf("%d", nx.olog[u]); printf(")"); } printf("\n"); } }
                if (kk >= 0 && getenv("GXLATER") && later[kk] <= 3) { printf("   later k'=%d run %d bits %d:", kk, nx.runlen, nx.co.bits); for (int q = 0; q < nx.nh; q++) { printf(" %s", nx.hist[q]); if (nx.lL[q] > -90) printf("[L%+.1f R%+.1f]", nx.lL[q], nx.lR[q]); } printf("\n"); }
                continue;
            }
        } else {
            if (!broken && nx.runlen > 0 && nx.rounds >= 1 && is_loop_state(sh) >= 0) {
                n_toloop++; if (nx.runlen > max_toloop_run) max_toloop_run = nx.runlen; continue;
            }
            if (broken) { n_exit++; if (nx.runlen > max_exit_run) max_exit_run = nx.runlen; exit_hist[nx.runlen < 63 ? nx.runlen : 63]++; record_new(&it.st); continue; }
            if (fin || (nx.rounds == 1 && nx.runlen == 0) || nx.nh >= HMAX) { n_exit++; if (nx.runlen > max_exit_run) max_exit_run = nx.runlen; exit_hist[nx.runlen < 63 ? nx.runlen : 63]++; continue; }
        }
        push(&nx);
    }
}

/* build a start state from a shape (marks after G) with ties, virtual geometry, and parities */
static int build(const char *shp, const char *tie, const long double *geo, int npos, int parmask, Item *root) {
    memset(root, 0, sizeof *root);
    /* variables: free marks in order, then E */
    int var_of[MAXM]; int nf = 0;
    for (int q = 0; q < npos; q++) var_of[q] = (tie[q] == 'F') ? nf++ : -1;
    nv = nf + 1; if (nv > NV) return 0;
    int vi = 0;
    for (int q = 0; q < npos; q++) if (tie[q] == 'F') X[vi++] = geo[q];
    X[nv - 1] = geo[npos];
    State *st = &root->st; memset(st, 0, sizeof *st);
    st->W = fvar(nv - 1);
    Form prev = fconst(0);
    S = *st;
    for (int q = 0; q < npos; q++) {
        Form f;
        if (tie[q] == 'F') f = fvar(var_of[q]);
        else if (tie[q] == 'C') f = fconst((ll)geo[q]);
        else if (tie[q] == 'E') f = faddc(S.W, (ll)geo[q]);
        else f = faddc(prev, (ll)geo[q]);
        add(shp[q + 1], f); prev = f;
    }
    add('G', fconst(1));
    root->st = S;
    for (int r = 0; r < nv; r++) { root->co.x0[r] = (parmask >> r) & 1; for (int c = 0; c < nv; c++) root->co.B[r][c] = (r == c) ? 2 : 0; }
    root->co.bits = 0; strcpy(root->hist[0], shp); root->nh = 1; sizes(&root->st, shp, &root->lL[0], &root->lR[0]);
    return 1;
}

static void report(const char *label) {
    printf("%s: ", label);
    if (MODE == 0) printf("P(pass) = %.10Lg (2^%.3Lf); ", p_pass, p_pass > 0 ? log2l(p_pass) : 0.0L);
    else printf("reach a loop state %lld times (run at most %d meetings by then); ", n_toloop, max_toloop_run);
    printf("ends %lld (run at most %d meetings); cut %lld; halts %lld; geometry-dependent comparisons %lld of %lld",
           n_exit, max_exit_run, n_cut, n_halt, geodep, ncmp);
    if (MODE == 0) { printf("; later loop stretches by k':"); for (int k = 0; k < 8; k++) if (later[k]) printf(" %d:%lld", k, later[k]); }
    printf("\n"); fflush(stdout);
}
static void reset_results(void) { p_pass = 0; n_exit = n_cut = n_halt = n_toloop = 0; max_exit_run = max_toloop_run = 0; memset(later, 0, sizeof later); memset(exit_hist, 0, sizeof exit_hist); geodep = ncmp = 0; }

static Item ROOT;
int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: see source\n"); return 1; }
    if (!strcmp(argv[1], "exit")) {
        MODE = 0; KX = atoi(argv[2]); CAP = atoi(argv[3]); NOSTOP = getenv("GXNOSTOP") != NULL;
        int npos = 3 + KX; long double geo[MAXM + 1]; char tie[MAXM]; char shp[16] = "G";
        for (int q = 0; q < npos; q++) { geo[q] = strtold(argv[4 + q], NULL); tie[q] = 'F'; strcat(shp, "W"); }
        geo[npos] = strtold(argv[4 + npos], NULL);
        int nvv = npos + 1;
        for (int pm = 0; pm < (1 << nvv); pm++) {
            reset_results(); CUR_PM = pm;
            if (!build(shp, tie, geo, npos, pm, &ROOT)) return 1;
            explore(&ROOT);
            if (p_pass == 0 && n_exit == 0) continue;
            char lab[64]; snprintf(lab, sizeof lab, "k=%d parities %x", KX, pm); report(lab);
            printf("   run lengths of exits:"); for (int i = 0; i < 64; i++) if (exit_hist[i]) printf(" %d:%lld", i, exit_hist[i]); printf("\n");
            printf("   loop stretches per run (paths, probability):"); for (int i = 0; i < 16; i++) if (chainhist[i]) printf(" %d:%lld/%.3Lg", i, chainhist[i], chainmass[i]); printf("\n");
            memset(chainhist, 0, sizeof chainhist); memset(chainmass, 0, sizeof chainmass);
            { long double tail = 0; printf("   P(run >= L):"); for (int L = 63; L >= 1; L--) { tail += runmass[L]; runmass[L] = tail; } for (int L = 1; L < 40; L++) if (runmass[L] > 0) printf(" %d:%.3Lg", L, runmass[L]); printf("\n"); memset(runmass, 0, sizeof runmass);
              tail = 0; printf("   P(run >= L, never in the plain loop):"); for (int L = 63; L >= 1; L--) { tail += runmass1[L]; runmass1[L] = tail; } for (int L = 1; L < 40; L++) if (runmass1[L] > 0) printf(" %d:%.3Lg", L, runmass1[L]); printf("\n"); memset(runmass1, 0, sizeof runmass1); }
        }
        return 0;
    }
    if (!strcmp(argv[1], "plat")) {   /* gx3 plat SHAPE ENDM MMAX CAP f_1 .. f_k : from a plateau state at its limit geometry */
        MODE = 3; PLAT = 1; const char *marks = argv[2]; int endm = atoi(argv[3]); MMAX = atoi(argv[4]); CAP = atoi(argv[5]);
        int npos = (int)strlen(marks); long double geo[MAXM + 1]; char tie[MAXM]; char shp[32] = "G"; strcat(shp, marks);
        long double W0 = ldexpl(1.0L, 50);
        int nfree = npos - (endm ? 1 : 0);
        if (argc < 6 + nfree) { fprintf(stderr, "need %d fractions\n", nfree); return 1; }
        for (int q = 0; q < nfree; q++) { geo[q] = floorl(strtold(argv[6 + q], NULL) * W0); tie[q] = 'F'; }
        if (endm) { geo[npos - 1] = -2; tie[npos - 1] = 'E'; }
        geo[npos] = W0;
        /* parity class from the stripe rules: a stripe between marks of equal value is odd, between different values even;
           the first mark follows the gap (value 0) at 1..3; the tape ends on a 1 */
        static const int LEN_[128] = { ['G'] = 3, ['M'] = 2, ['W'] = 2, ['B'] = 3 }; static const int VAL_[128] = { ['G'] = 0, ['M'] = 1, ['W'] = 0, ['B'] = 1 };
        int par[MAXM + 1]; int prevval = 0, prevend = 4;   /* position parity of the cell after the previous mark */
        for (int q = 0; q < npos; q++) { int v = VAL_[(int)marks[q]]; par[q] = (prevend + (v == prevval ? 1 : 0)) & 1; prevend = (par[q] + LEN_[(int)marks[q]]) & 1; prevval = v; }
        int parE;
        if (endm) parE = par[npos - 1];                            /* the end marker sits at E - 2 */
        else parE = (prevend + (prevval == 0 ? 1 : 0)) & 1;         /* T = E - end odd iff the last mark is a 0-mark */
        int pm = 0; { int vi = 0; for (int q = 0; q < npos; q++) if (tie[q] == 'F') { if (par[q]) pm |= 1 << vi; vi++; } if (parE) pm |= 1 << vi; }
        long long cut_tot = 0, exit_tot = 0, gd_tot = 0, nc_tot = 0; S2 = 0;
        reset_results();
        if (!build(shp, tie, geo, npos, pm, &ROOT)) { fprintf(stderr, "build failed\n"); return 1; }
        explore(&ROOT); cut_tot += n_cut; gd_tot += geodep; nc_tot += ncmp; exit_tot = n_exit;
        printf("start %s%s parity class %d: plain entries %lld, run ends %lld, more than %d extra-wall passes %lld, cut %lld; geometry-dependent comparisons %lld of %lld\n",
               shp, endm ? " (end marker tied)" : "", pm, n_entry, exit_tot, MMAX, n_more, cut_tot, gd_tot, nc_tot);
        for (int m = 0; m <= MMAX; m++) {
            printf("after %d extra-wall passes: entry measure %.4Lg, largest sigma %.3Lf; P(sigma >= x):", m, emass_tot[m], emax[m]);
            long double tail = 0; for (int b = SB - 1; b >= 0; b--) { tail += emass[m][b]; if (emass[m][b] > 0 && b % 2 == 0) printf(" %d:%.3Lg", b, tail); }
            printf("\n");
            for (int t = 0; t < ntops[m]; t++) { Top *T = &tops[m][t]; printf("   sigma %.3Lf (s %.3Lf, lambda %.3Lf), bits %d: %s\n", T->sig, T->s, T->lam, T->bits, T->word); }
        }
        return 0;
    }
    if (!strcmp(argv[1], "xlead")) {   /* gx2 xlead K MMAX CAP X0 .. X_{nv-1} */
        MODE = 3; KX = atoi(argv[2]); MMAX = atoi(argv[3]); CAP = atoi(argv[4]);
        int npos = 3 + KX; long double geo[MAXM + 1]; char tie[MAXM]; char shp[16] = "G";
        for (int q = 0; q < npos; q++) { geo[q] = strtold(argv[5 + q], NULL); tie[q] = 'F'; strcat(shp, "W"); }
        geo[npos] = strtold(argv[5 + npos], NULL);
        int nvv = npos + 1, ncls = 0; long long cut_tot = 0, exit_tot = 0, gd_tot = 0, nc_tot = 0; S2 = log2l(geo[npos] / (geo[npos] - geo[npos - 1]));
        int vmask = 0; for (int q = 0; q < npos; q++) if (q % 2 == 0) vmask |= 1 << q;
        if (!((vmask >> (npos - 1)) & 1)) vmask |= 1 << npos;   /* E odd when the last wall is even */
        for (int pm = vmask; pm <= vmask; pm++) {   /* the one parity class that is a real tape */
            long long e0 = n_entry, x0 = n_exit, m0 = n_more; reset_results();
            if (!build(shp, tie, geo, npos, pm, &ROOT)) return 1;
            explore(&ROOT); cut_tot += n_cut; gd_tot += geodep; nc_tot += ncmp;
            if (n_entry > e0 || n_exit > 0 || n_more > m0) ncls++; exit_tot += n_exit;
        }
        long double E = geo[npos], d = geo[npos - 1];
        printf("start %s, lateness s2 = log2(E/(E-d)) = %.3Lf; valid parity classes %d; plain entries %lld, run ends %lld, more than %d passes %lld, cut %lld; geometry-dependent comparisons %lld of %lld\n",
               shp, log2l(E / (E - d)), ncls, n_entry, exit_tot, MMAX, n_more, cut_tot, gd_tot, nc_tot);
        { long double tail = 0; printf("plain entries by meetings j between the start and the entry (s = s2 + j): P(j >= J), largest lambda at that j:");
          for (int j = 63; j >= 0; j--) { tail += jmass[j]; if (jmass[j] > 0) printf(" %d:%.3Lg/%.2Lf", j, tail / ncls, jlam[j]); } printf("\n"); }
        for (int m = 0; m <= MMAX; m++) {
            printf("after %d extra-wall passes: entry measure %.4Lg, largest sigma %.3Lf; P(sigma >= x):", m, emass_tot[m] / ncls, emax[m]);
            long double tail = 0; for (int b = SB - 1; b >= 0; b--) { tail += emass[m][b]; if (emass[m][b] > 0 && b % 2 == 0) printf(" %d:%.3Lg", b, tail / ncls); }
            printf("\n");
            for (int t = 0; t < ntops[m]; t++) { Top *T = &tops[m][t]; printf("   sigma %.3Lf (s %.3Lf, lambda %.3Lf), bits %d, R1 =", T->sig, T->s, T->lam, T->bits);
                for (int j = 0; j < nv; j++) if (T->beta[j] != 0) printf(" %+g*t%d", T->beta[j], j + 1); printf(" %+g: %s\n", T->b0, T->word);
                if (t == 0) { i128 y[NV], x[NV]; printf("      integer point:");
                    for (int r = 0; r < nv; r++) { i128 acc = T->co.x0[r]; for (int c = 0; c < r; c++) acc += T->co.B[r][c] * y[c];
                        long double want = X[r] - (long double)acc; y[r] = (i128)llroundl(want / (long double)T->co.B[r][r]); x[r] = acc + T->co.B[r][r] * y[r]; printf(" %lld", (ll)x[r]); }
                    printf("\n"); } }
        }
        return 0;
    }
    if (!strcmp(argv[1], "endgame")) {   /* gx2 endgame Rmin Rmax CAP a b E [parity mask, default 1 = a odd] */
        MODE = 4; int R0 = atoi(argv[2]), R1 = atoi(argv[3]); CAP = atoi(argv[4]); NOPHASE = getenv("GXNOPHASE") != NULL; em_maxmeet = em_maxmeet_close = 0;
        long double geo[4] = { strtold(argv[5], NULL), strtold(argv[6], NULL), 0, strtold(argv[7], NULL) };
        int pm = argc > 8 ? atoi(argv[8]) : 1;
        char tie[3] = { 'F', 'F', 'E' };
        long long gd_tot = 0, nc_tot = 0; int closing[4096], ncl = 0;
        for (int R = R0; R <= R1; R += 2) {
            geo[2] = -(R + 1);
            em_close = em_break = em_pass = em_np0 = em_bad = em_halt = em_cut = em_limit = 0;
            ec_close = ec_break = ec_pass = ec_np0 = ec_bad = ec_halt = ec_cut = ec_limit = 0; geodep = ncmp = 0;
            if (!build("GWWW", tie, geo, 3, pm, &ROOT)) return 1;
            explore_end(&ROOT, R);
            gd_tot += geodep; nc_tot += ncmp;
            if (ec_close || ec_bad || ec_halt || ec_cut || ec_limit || getenv("GXALLR"))
                printf("R %d: close %.6Lg (%lld), break %.4Lg (%lld), pass %.4Lg (%lld), notphase0 %.4Lg (%lld), bad %.3Lg (%lld), halt %lld, cut %lld, limit %lld, geometry-dependent %lld\n",
                       R, em_close, ec_close, em_break, ec_break, em_pass, ec_pass, em_np0, ec_np0, em_bad, ec_bad, ec_halt, ec_cut, ec_limit, geodep);
            if (ec_close && ncl < 4096) closing[ncl++] = R;
        }
        printf("closing R:"); for (int i = 0; i < ncl; i++) printf(" %d", closing[i]);
        printf("\ngeometry-dependent comparisons %lld of %lld; most end meetings from the start before a break or a new pass: %d; before a close: %d\n", gd_tot, nc_tot, em_maxmeet, em_maxmeet_close);
        return 0;
    }
    if (!strcmp(argv[1], "line")) {      /* gx line n0 s cap : the clean tape class n = n0 (mod 2^s), whole cycle */
        MODE = 2; ll n0 = atoll(argv[2]); int s0 = atoi(argv[3]); CAP = atoi(argv[4]);
        long double geo[2] = { -2, 1e18L }; char tie[1] = { 'E' };
        build("GM", tie, geo, 1, 0, &ROOT);
        ROOT.co.x0[0] = (i128)(2 * n0 + 6) % ((i128)1 << (s0 + 1)); ROOT.co.B[0][0] = (i128)1 << (s0 + 1); ROOT.co.bits = 0;
        explore(&ROOT);
        printf("class %lld mod 2^%d: paths %lld, cut %lld, halts %lld, longest run %d, geometry-dependent %lld/%lld\n", n0, s0, n_exit, n_cut, n_halt, max_exit_run, geodep, ncmp);
        printf("   most loop stretches in one run (paths/probability):"); for (int i = 0; i < 8; i++) if (linest[i]) printf(" %d:%lld/%.3Lg", i, linest[i], linestm[i]); printf("\n");
        long double tail = 0; printf("   P(longest run >= L):"); for (int L = 63; L >= 1; L--) { tail += linemass[L]; linemass[L] = tail; } for (int L = 1; L < 40; L++) if (linemass[L] > 0) printf(" %d:%.3Lg", L, linemass[L]); printf("\n");
        return 0;
    }
    if (!strcmp(argv[1], "point")) {      /* follow one integer point: gx point SHAPE x1 .. xm E rounds */
        MODE = 1; CAP = 0; const char *shp = argv[2]; int npos = (int)strlen(shp) - 1;
        long double geo[MAXM + 1]; char tie[MAXM];
        for (int q = 0; q <= npos; q++) geo[q] = strtold(argv[3 + q], NULL);
        for (int q = 0; q < npos; q++) tie[q] = 'F';
        build(shp, tie, geo, npos, 0, &ROOT);
        for (int r = 0; r < nv; r++) { ROOT.co.x0[r] = (i128)geo[r < nv - 1 ? r : npos]; for (int c = 0; c < nv; c++) ROOT.co.B[r][c] = (r == c) ? ((i128)1 << 70) : 0; }
        int rounds = atoi(argv[4 + npos]);
        Item it = ROOT;
        for (int r = 0; r < rounds; r++) {
            S = it.st; CO = &it.co; FORCED = it.forced; NFORCED = 0; FI = 0; NEEDBR = 0;
            do_round(); if (NEEDBR) { printf("undecided?\n"); break; } if (S.bad || S.halted) { printf("bad %d halted %d\n", S.bad, S.halted); break; }
            it.st = S; char sh[16]; shape(&S, sh, NULL, NULL); printf(" %s", sh);
        }
        printf("\n"); return 0;
    }
    if (!strcmp(argv[1], "run")) {
        MODE = 1; CAP = atoi(argv[2]); const char *shp = argv[3]; int npos = (int)strlen(shp) - 1;
        long double geo[MAXM + 1]; char tie[MAXM];
        for (int q = 0; q < npos; q++) { geo[q] = strtold(argv[4 + q], NULL); tie[q] = 'F'; }
        geo[npos] = strtold(argv[4 + npos], NULL);
        for (int q = 0; q < npos; q++) if (shp[q + 1] == 'M' && geo[q] == geo[npos] - 2) { tie[q] = 'E'; geo[q] = -2; }
        int nvv = 1; for (int q = 0; q < npos; q++) if (tie[q] == 'F') nvv++;
        for (int pm = 0; pm < (1 << nvv); pm++) {
            reset_results(); nnew = 0;
            if (!build(shp, tie, geo, npos, pm, &ROOT)) return 1;
            explore(&ROOT);
            if (n_toloop == 0 && n_exit == 0) continue;
            char lab[64]; snprintf(lab, sizeof lab, "%s parities %x", shp, pm); report(lab);
            printf("   next-run shapes:"); for (int i = 0; i < nnew; i++) printf(" %s", newsh[i]); printf("\n");
        }
        return 0;
    }
    if (!strcmp(argv[1], "closure")) {
        MODE = 1; CAP = atoi(argv[2]);
        static char qsh[512][16]; static long double qgeo[512][MAXM + 1]; static char qtie[512][MAXM]; static int qn[512]; int nq = 0, qi = 0;
        static char done[512][16]; int nd = 0;
        /* clean tape: G, end marker at W - 2 */
        strcpy(qsh[0], "GM"); qn[0] = 1; qtie[0][0] = 'E'; qgeo[0][0] = -2; qgeo[0][1] = 1e18L; nq = 1;
        while (qi < nq) {
            char *shp = qsh[qi]; int npos = qn[qi];
            int seen = 0; for (int i = 0; i < nd; i++) if (!strcmp(done[i], shp)) seen = 1;
            if (seen) { qi++; continue; }
            strcpy(done[nd++], shp);
            int nvv = 1; for (int q = 0; q < npos; q++) if (qtie[qi][q] == 'F') nvv++;
            long long tl = 0, te = 0, tc = 0, th = 0, tg = 0, tcmp = 0; int ml = 0, me = 0;
            static char agg[NNEW][16]; int na = 0;
            for (int pm = 0; pm < (1 << nvv); pm++) {
                reset_results(); nnew = 0;
                if (!build(shp, qtie[qi], qgeo[qi], npos, pm, &ROOT)) { printf("too many variables for %s\n", shp); break; }
                explore(&ROOT);
                tl += n_toloop; te += n_exit; tc += n_cut; th += n_halt; tg += geodep; tcmp += ncmp;
                if (max_toloop_run > ml) ml = max_toloop_run; if (max_exit_run > me) me = max_exit_run;
                for (int i = 0; i < nnew; i++) {
                    int f = 0; for (int j = 0; j < na; j++) if (!strcmp(agg[j], newsh[i])) f = 1;
                    if (!f && na < NNEW) strcpy(agg[na++], newsh[i]);
                    int inq = 0; for (int j = 0; j < nq; j++) if (!strcmp(qsh[j], newsh[i])) inq = 1;
                    if (!inq && nq < 512) { strcpy(qsh[nq], newsh[i]); qn[nq] = newnpos[i]; memcpy(qtie[nq], newtie[i], MAXM); memcpy(qgeo[nq], newgeo[i], sizeof(long double) * (MAXM + 1)); nq++; }
                }
            }
            printf("%-10s ties %.*s | to loop %lld (within %d) | ends %lld (within %d) | cut %lld | halts %lld | geom-dep %lld/%lld | next:",
                   shp, npos, qtie[qi], tl, ml, te, me, tc, th, tg, tcmp);
            for (int j = 0; j < na; j++) printf(" %s", agg[j]); printf("\n"); fflush(stdout);
            qi++;
        }
        printf("closed after %d shapes\n", nd);
        return 0;
    }
    return 1;
}
