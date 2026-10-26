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
    if (!getenv("NOHNF")) hnf(C);
}

/* ---- model ---- */
typedef struct {
    char T[MAXM]; Form P[MAXM]; char A[MAXM]; int nm; Form W; int halted, bad;
    int nmeet; Form md[8]; char mres[8]; char mlast[8];      /* meetings in the current round */
} State;
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
static int test(Form d) {
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
    char hist[HMAX][16]; int nh;
    int runlen; Form rlast; int rres; int started;
} Item;
static Item *stack_; static long long sp, scap;
static void push(const Item *it) {
    if (sp >= scap) { scap = scap ? scap * 2 : 1024; stack_ = realloc(stack_, sizeof(Item) * scap); if (!stack_) { fprintf(stderr, "out of memory\n"); exit(1); } }
    stack_[sp++] = *it;
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

/* mode: 0 exit(K), 1 run-start */
static int MODE, KX, CAP;
static void explore(Item *root) {
    sp = 0; push(root);
    while (sp > 0) {
        Item it = stack_[--sp];
        S = it.st; CO = &it.co; FORCED = it.forced; NFORCED = it.nf; FI = 0; NEEDBR = 0; DBGROUND = (it.nh <= 3);
        do_round();
        if (NEEDBR) {
            if (it.co.bits + it.nf + 1 > CAP) { n_cut++; continue; }
            Item a = it; a.forced[a.nf++] = 0; push(&a);
            Item b = it; b.forced[b.nf++] = 2; push(&b);
            continue;
        }
        if (S.bad) { if (getenv("GXDEBUG") && nbad < 6) { printf("   bad %d after:", S.bad); for (int q = 0; q < it.nh; q++) printf(" %s", it.hist[q]); printf(" bits %d\n", it.co.bits); } nbad++; continue; }
        if (S.halted) { n_halt++; continue; }
        Item nx = it; nx.st = S; nx.nf = 0; nx.rounds++;
        char sh[16]; shape(&S, sh, NULL, NULL);
        if (nx.nh < HMAX) strcpy(nx.hist[nx.nh++], sh);
        int broken = 0;
        for (int q = 0; q < S.nmeet; q++) {
            if (nx.started && !feq(pred(nx.rlast, nx.rres), S.md[q])) {
                if (MODE == 1 && nx.rounds == 1) { nx.runlen = 0; }
                else { broken = 1; break; }
            }
            nx.started = 1; nx.runlen++; nx.rlast = S.md[q]; nx.rres = S.mres[q];
        }
        int fin = is_clean(&S);
        if (MODE == 0) {
            if (nx.nh == 9 && !broken) {
                int okp = 0; char s[16];
                for (int ph = 0; ph < 8; ph += 6) { int all = 1; for (int q = 0; q < 9; q++) { loopshape(KX, ph + q, s); if (strcmp(nx.hist[q], s)) { all = 0; break; } } if (all) okp = 1; }
                if (okp) { p_pass += ldexpl(1.0L, -nx.co.bits); continue; }
            }
            if (broken || fin || nx.nh >= HMAX) {
                if (getenv("GXDEBUG") && (n_exit < 12 || getenv("GXALL"))) { printf("   exit run %d bits %d broken %d fin %d:", nx.runlen, nx.co.bits, broken, fin); for (int q = 0; q < nx.nh; q++) printf(" %s", nx.hist[q]); printf("\n"); }
                n_exit++; if (nx.runlen > max_exit_run) max_exit_run = nx.runlen; exit_hist[nx.runlen < 63 ? nx.runlen : 63]++;
                /* rounds following the k-loop from the start */
                int pre = 0; char s[16];
                for (int ph = 0; ph < 8; ph += 6) { int q = 0; while (q < nx.nh) { loopshape(KX, ph + q, s); if (strcmp(nx.hist[q], s)) break; q++; } if (q > pre) pre = q; }
                int kk = later_loop(&nx, pre); if (kk >= 0) later[kk]++;
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
    root->co.bits = 0; strcpy(root->hist[0], shp); root->nh = 1;
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
        MODE = 0; KX = atoi(argv[2]); CAP = atoi(argv[3]);
        int npos = 3 + KX; long double geo[MAXM + 1]; char tie[MAXM]; char shp[16] = "G";
        for (int q = 0; q < npos; q++) { geo[q] = strtold(argv[4 + q], NULL); tie[q] = 'F'; strcat(shp, "W"); }
        geo[npos] = strtold(argv[4 + npos], NULL);
        int nvv = npos + 1;
        for (int pm = 0; pm < (1 << nvv); pm++) {
            reset_results();
            if (!build(shp, tie, geo, npos, pm, &ROOT)) return 1;
            explore(&ROOT);
            if (p_pass == 0 && n_exit == 0) continue;
            char lab[64]; snprintf(lab, sizeof lab, "k=%d parities %x", KX, pm); report(lab);
            printf("   run lengths of exits:"); for (int i = 0; i < 64; i++) if (exit_hist[i]) printf(" %d:%lld", i, exit_hist[i]); printf("\n");
        }
        return 0;
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
