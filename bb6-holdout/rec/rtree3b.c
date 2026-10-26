/* Exact 2-adic route tree from a free GMM state (gap at 1, marker m, end marker at E - 2), the C version of
   ../conc/fasttree.py: every branch of the mark model's d (mod 4) tests is followed on cosets of (m, E), order
   comes from the asymptotic point m/E = 1/2 (value of a form a m + b E + c at m = 2^119, E = 2^120 + 1: compared by
   a + 2b, then b + c), and every prefix that ends at G W W W or G W W W W is printed with its coset size.
   usage: rtree cut_bits [part nparts split_bits] > out      lines: "W bits shapes... | outs..." or "X ..." */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
typedef long long ll; typedef __int128 i128;
#define MAXM 48
#define MAXR 200
#define MAXO 1200
typedef struct { ll a, b, c; int e; } Form;               /* (a m + b E + c) / 2^e */
static int ctzll_(unsigned long long x) { return x ? __builtin_ctzll(x) : 64; }
static Form norm(Form f) {
    while (f.e > 0 && !((f.a | f.b | f.c) & 1)) { f.a /= 2; f.b /= 2; f.c /= 2; f.e--; }
    return f;
}
static Form fconst(ll k) { Form f = {0, 0, k, 0}; return f; }
static Form fadd(Form f, ll k) { f.c += k * (1LL << f.e); return f; }
static Form fplus(Form p, Form q, int sgn) {
    int e = p.e > q.e ? p.e : q.e; Form r;
    if (e > 60) { fprintf(stderr, "exponent overflow\n"); exit(3); }
    ll sp = 1LL << (e - p.e), sq = 1LL << (e - q.e);
    r.a = p.a * sp + sgn * (q.a * sq);
    r.b = p.b * sp + sgn * (q.b * sq);
    r.c = p.c * sp + sgn * (q.c * sq);
    r.e = e; return norm(r);
}
static Form fhalf(Form f) { f.e++; return norm(f); }
/* compare values at the asymptotic point */
static ll RP = 1, RS = 1;   /* ratio m/E = RP / 2^RS */
static int fcmp(Form p, Form q) {
    int e = p.e > q.e ? p.e : q.e;
    i128 sp = (i128)1 << (e - p.e), sq = (i128)1 << (e - q.e);
    i128 k1p = ((i128)p.a * RP + ((i128)p.b << RS)) * sp, k1q = ((i128)q.a * RP + ((i128)q.b << RS)) * sq;
    if (k1p != k1q) return k1p < k1q ? -1 : 1;
    i128 k2p = (i128)(p.b + p.c) * sp, k2q = (i128)(q.b + q.c) * sq;
    if (k2p != k2q) return k2p < k2q ? -1 : 1;
    return 0;
}
static int fcmpk(Form p, ll k) { return fcmp(p, fconst(k)); }

typedef struct { ll x0[2]; ll B[2][2]; int bits; } Coset;
static int cerr;    /* set on non-integral form / odd distance: the path is dropped (as AssertionError in Python) */
static int evalf(const Coset *C, Form f, i128 *f0, i128 g[2]) {
    i128 a0 = (i128)f.c + (i128)f.a * C->x0[0] + (i128)f.b * C->x0[1];
    i128 g0 = (i128)f.a * C->B[0][0] + (i128)f.b * C->B[1][0];
    i128 g1 = (i128)f.a * C->B[0][1] + (i128)f.b * C->B[1][1];
    i128 den = (i128)1 << f.e;
    if ((a0 % den) || (g0 % den) || (g1 % den)) { cerr = 1; return 0; }
    *f0 = a0 / den; g[0] = g0 / den; g[1] = g1 / den; return 1;
}
static int decided(const Coset *C, Form f) {      /* -1 undecided, else f0 mod 4 */
    i128 f0, g[2]; if (!evalf(C, f, &f0, g)) return -2;
    if (((g[0] >> 1) & 1) == 0 && ((g[1] >> 1) & 1) == 0) { int r = (int)(f0 % 4); if (r < 0) r += 4; return r; }
    return -1;
}

static i128 floordiv(i128 a, i128 b) { i128 q = a / b; if ((a % b != 0) && ((a < 0) != (b < 0))) q--; return q; }
static void hnf(Coset *C) {
    i128 u0 = C->B[0][0], u1 = C->B[1][0], v0 = C->B[0][1], v1 = C->B[1][1];
    /* extended gcd of u0, v0 */
    i128 a = u0, b = v0, x0 = 1, y0 = 0, x1 = 0, y1 = 1;
    while (b != 0) { i128 q = floordiv(a, b), t; t = a - q * b; a = b; b = t; t = x0 - q * x1; x0 = x1; x1 = t; t = y0 - q * y1; y0 = y1; y1 = t; }
    if (a < 0) { a = -a; x0 = -x0; y0 = -y0; }
    i128 g = a;
    i128 c1a = g, c1b = x0 * u1 + y0 * v1;                         /* x0*u + y0*v */
    i128 c2b = (v0 / g) * u1 - (u0 / g) * v1;                      /* (v0/g) u - (u0/g) v, first comp 0 */
    if (c2b < 0) c2b = -c2b;
    i128 q = floordiv(c1b, c2b); c1b -= q * c2b;
    C->B[0][0] = (ll)c1a; C->B[1][0] = (ll)c1b; C->B[0][1] = 0; C->B[1][1] = (ll)c2b;
    i128 X0 = C->x0[0], X1 = C->x0[1];
    i128 k = floordiv(X0, c1a); X0 -= k * c1a; X1 -= k * c1b;
    k = floordiv(X1, c2b); X1 -= k * c2b;
    C->x0[0] = (ll)X0; C->x0[1] = (ll)X1;
}
static void impose(Coset *C, Form f, int res) {
    i128 f0, g[2]; if (!evalf(C, f, &f0, g)) return;
    if ((f0 & 1) || (g[0] & 1) || (g[1] & 1)) { cerr = 1; return; }
    i128 h[2] = {g[0] / 2, g[1] / 2};
    i128 tt = (res - f0) / 2; int t = (int)(tt % 2); if (t < 0) t += 2;
    int i = (h[0] & 1) ? 0 : ((h[1] & 1) ? 1 : -1);
    if (i < 0) return;     /* decided; never called in that case */
    for (int r = 0; r < 2; r++) C->x0[r] += (ll)t * C->B[r][i];
    for (int k = 0; k < 2; k++) if (k != i) for (int r = 0; r < 2; r++) C->B[r][k] -= (ll)h[k] * C->B[r][i];
    for (int r = 0; r < 2; r++) C->B[r][i] *= 2;
    C->bits++;
    hnf(C);
    for (int r = 0; r < 2; r++) for (int k = 0; k < 2; k++) if (llabs(C->B[r][k]) > (1LL << 60)) { fprintf(stderr, "coset overflow\n"); exit(3); }
}

typedef struct {
    char T[MAXM]; Form P[MAXM]; char A[MAXM]; int nm; Form W; int halted, bad;
    unsigned char outs[MAXO]; int nout; double maxH; int seenW; Form lastd; int lastres, haslast; double maxHrun;
    int g4; Form gB, gC, gW;
} St;
static St S; static Coset *CC; static const unsigned char *FRC; static int NFRC, FI; static int BRANCH;
static int addm(char t, Form p) {
    for (int i = 0; i < S.nm; i++) if (!S.A[i]) { S.T[i] = t; S.P[i] = p; S.A[i] = 1; return i; }
    if (S.nm >= MAXM) { S.bad = 9; return 0; }
    S.T[S.nm] = t; S.P[S.nm] = p; S.A[S.nm] = 1; return S.nm++;
}
static int last_mark(void) { int b = -1; for (int i = 0; i < S.nm; i++) if (S.A[i] && (b < 0 || fcmp(S.P[i], S.P[b]) > 0)) b = i; return b; }
static double Hmax_global = 0, Hmax_noW = 0, Hmax_run = 0; static int unboundedH = 0;
static double formH(Form d) {   /* log2 (1 / min over 0<t<1 of (a t + b) / 2^e) */
    ll lo = d.b < d.a + d.b ? d.b : d.a + d.b;
    if (lo <= 0) return 1e9;
    return d.e - __builtin_log2((double)lo);
}
static int first_right(Form x) { int b = -1; for (int i = 0; i < S.nm; i++) if (S.A[i] && fcmp(S.P[i], x) > 0 && (b < 0 || fcmp(S.P[i], S.P[b]) < 0)) b = i; return b; }
static int packet_back(Form x) {
    int b = -1;
    for (int i = 0; i < S.nm; i++) if (S.A[i] && S.T[i] != 'M' && fcmp(S.P[i], x) < 0 && (b < 0 || fcmp(S.P[i], S.P[b]) > 0)) b = i;
    if (b < 0) return -1;
    if (S.T[b] == 'B') { S.halted = 1; return -1; }
    if (S.T[b] == 'G') { S.P[b] = fadd(S.P[b], 2); return b; }
    Form q = S.P[b]; S.T[b] = 'M'; S.P[b] = fadd(q, -1); return addm('G', fadd(q, 1));
}
static int shift_from(Form x) {
    int k = first_right(x);
    if (k < 0) { S.W = fadd(S.W, 2); addm('M', fadd(S.W, -2)); return packet_back(fadd(S.W, -2)); }
    char t = S.T[k];
    if (t == 'M') { S.T[k] = 'G'; return k; }
    if (t == 'W') { S.T[k] = 'B'; return packet_back(S.P[k]); }
    if (t == 'B') { S.T[k] = 'W'; S.P[k] = fadd(S.P[k], 2); return packet_back(S.P[k]); }
    S.bad = 2; return -1;
}
static int test_outcome(Form d) {
    int dec = decided(CC, d);
    if (dec == -2) return -1;
    if (dec >= 0) return dec;
    if (FI < NFRC) { int r = FRC[FI++]; impose(CC, d, r); return cerr ? -1 : r; }
    BRANCH = 1; return -1;
}
static void do_round(void) {
    int gap = -1;
    for (int i = 0; i < S.nm; i++) if (S.A[i] && S.T[i] == 'G' && fcmpk(S.P[i], 1) == 0) gap = i;
    while (gap >= 0 && !S.halted && !S.bad) {
        Form g = S.P[gap]; int m = first_right(g);
        if (m < 0) { S.A[gap] = 0; S.W = fadd(S.W, 3); addm('M', fadd(S.W, -2)); gap = packet_back(fadd(S.W, -2)); continue; }
        char t = S.T[m];
        if (t == 'M') {
            Form d = fadd(fplus(S.P[m], g, -1), -3);
            if (fcmpk(d, 0) < 0) { S.bad = 3; return; }
            int islast = (m == last_mark());
            int res = test_outcome(d);
            if (res < 0) return;          /* branch or dropped path */
            if (islast && !S.seenW) { double h = formH(d); if (h > S.maxH) S.maxH = h; }
            if (islast) {
                int cont = 0;
                if (S.haslast) { Form pd = S.lastres == 2 ? fhalf(fadd(S.lastd, -2)) : fadd(fhalf(S.lastd), 4);
                                 cont = (pd.a == d.a && pd.b == d.b && pd.c == d.c && pd.e == d.e); }
                if (!cont) S.seenW = 0;          /* a new run starts: reset the loop flag for this run */
                S.lastd = d; S.lastres = res; S.haslast = 1;
                if (!S.seenW) { double h = formH(d); if (h > S.maxHrun) S.maxHrun = h; }
            }
            if (S.nout < MAXO) S.outs[S.nout++] = (unsigned char)res; else { S.bad = 8; return; }
            if (res == 0) { Form h = fhalf(d); S.P[m] = fadd(fplus(g, h, 1), -1); S.P[gap] = fadd(fplus(g, h, 1), 1); }
            else { S.A[gap] = 0; S.T[m] = 'W'; S.P[m] = fadd(fplus(g, fhalf(d), 1), 3); gap = packet_back(S.P[m]); }
        } else if (t == 'W') { Form x = S.P[m]; S.A[gap] = 0; S.A[m] = 0; gap = shift_from(x); }
        else if (t == 'B') { S.T[m] = 'W'; S.P[m] = fadd(S.P[m], -1); gap = shift_from(S.P[m]); }
        else { S.bad = 4; return; }
    }
    ll extra = 2;
    for (int i = 0; i < S.nm; i++) if (S.A[i] && S.T[i] == 'M' && fcmpk(S.P[i], 0) == 0) { S.T[i] = 'W'; S.P[i] = fconst(1); extra = 4; }
    for (int i = 0; i < S.nm; i++) if (S.A[i]) S.P[i] = fadd(S.P[i], extra);
    S.W = fadd(S.W, extra); addm('G', fconst(1));
}

/* ---- sigma ceiling of a plain entry: sigma(t) = -3 log2(R1/E) + 2 log2(|L1|/E) at m = tE, maximised over 0 < t < 1 ---- */
#define NSB 120
static long double sig_mass[NSB]; static long long sig_cnt[NSB]; static double sig_top = 0; static long double meas_entries = 0;
static double SIGPRINT = 1e9;
static double fv(Form f, double t) { return ((double)f.a * t + (double)f.b) / ldexp(1.0, f.e); }
static double sigma_max(Form B, Form C, Form W, double *targ) {
    double best = -1e9; *targ = 0;
    for (int i = 0; i <= 1024; i++) {
        double t = i / 1024.0;
        double w = fv(W, t), r = w - fv(C, t), l = 147 * fv(B, t) + 280 * w - 392 * fv(C, t);
        if (r <= 0) { *targ = t; return 1e9; }
        if (l == 0) continue;
        double sg = 3 * log2(w / r) + 2 * log2(fabs(l) / w);
        if (sg > best) { best = sg; *targ = t; }
    }
    return best;
}
static long long nhalted = 0, nbadp[16];
static int order[MAXM], nord;
static void sortmarks(void) {
    nord = 0; for (int i = 0; i < S.nm; i++) if (S.A[i]) order[nord++] = i;
    for (int i = 1; i < nord; i++) { int v = order[i], j = i - 1; while (j >= 0 && fcmp(S.P[order[j]], S.P[v]) > 0) { order[j + 1] = order[j]; j--; } order[j + 1] = v; }
}

typedef struct Node { St st; Coset c; unsigned char forced[64]; int nf; int rd; int hlen; struct Node *next; } Node;
/* shape history kept as a string per node: store in a separate growing buffer referenced by offset */
static char **HIST; static int *HLEN;
int main(int argc, char **argv) {
    int cut = atoi(argv[1]); int part = argc > 2 ? atoi(argv[2]) : 0, nparts = argc > 3 ? atoi(argv[3]) : 1;
    int split = argc > 4 ? atoi(argv[4]) : 10;
    if (argc > 6) { RP = atoll(argv[5]); RS = atoll(argv[6]); }
    if (getenv("SIGPRINT")) SIGPRINT = atof(getenv("SIGPRINT"));
    /* explicit stack */
    int cap = 1 << 12, top = 0;
    Node *stk = malloc(sizeof(Node) * cap); char **hst = malloc(sizeof(char *) * cap);
    Node n0; memset(&n0, 0, sizeof n0);
    S.nm = 0; S.halted = 0; S.bad = 0; S.nout = 0; S.maxH = 0; S.seenW = 0; S.haslast = 0; S.maxHrun = 0;
    Form Wf = {0, 1, 0, 0}; S.W = Wf;
    addm('G', fconst(1)); Form mf = {1, 0, 0, 0}; addm('M', mf); addm('M', fadd(S.W, -2));
    n0.st = S; n0.c.x0[0] = 0; n0.c.x0[1] = 1; n0.c.B[0][0] = 2; n0.c.B[0][1] = 0; n0.c.B[1][0] = 0; n0.c.B[1][1] = 2; n0.c.bits = 0;
    n0.nf = 0; n0.rd = 0;
    stk[top] = n0; hst[top] = strdup(""); top++;
    long double lost = 0; long long nW = 0, nX = 0, splitc = 0, ndrop = 0;
    char shape[MAXM + 1];
    while (top > 0) {
        top--; Node nd = stk[top]; char *hist = hst[top];
        S = nd.st; Coset c = nd.c; CC = &c; FRC = nd.forced; NFRC = nd.nf; FI = 0; BRANCH = 0; cerr = 0;
        do_round();
        if (BRANCH) {
            int nb = nd.c.bits + nd.nf + 1;
            if (nb > cut) { lost += 1.0L / (long double)((i128)1 << (nd.c.bits + nd.nf)); free(hist); continue; }
            int pushed = 0;
            for (int oi = 0; oi < 2; oi++) {
                int o = oi == 0 ? 2 : 0;
                if (nparts > 1 && nb == split) { splitc++; if (splitc % nparts != part) continue; }
                if (top + 1 >= cap) { cap *= 2; stk = realloc(stk, sizeof(Node) * cap); hst = realloc(hst, sizeof(char *) * cap); }
                stk[top] = nd; stk[top].forced[nd.nf] = (unsigned char)o; stk[top].nf = nd.nf + 1;
                hst[top] = pushed ? strdup(hist) : hist; pushed = 1; top++;
            }
            if (!pushed) free(hist);
            continue;
        }
        if (cerr) { ndrop++; free(hist); continue; }
        if (S.maxH > Hmax_global) Hmax_global = S.maxH;
        if (S.maxHrun > Hmax_run) Hmax_run = S.maxHrun;
        if (S.halted) nhalted++; else if (S.bad) nbadp[S.bad < 15 ? S.bad : 15]++;
        if (S.halted || S.bad) { if (!S.seenW && S.maxH > Hmax_noW) Hmax_noW = S.maxH; free(hist); continue; }
        sortmarks(); for (int i = 0; i < nord; i++) shape[i] = S.T[order[i]]; shape[nord] = 0;
        if ((!strcmp(shape, "GM") && fcmp(S.P[order[1]], fadd(S.W, -2)) == 0) || (!strcmp(shape, "GMM") && fcmp(S.P[order[2]], fadd(S.W, -2)) == 0)) {
            if (!S.seenW && S.maxH > Hmax_noW) Hmax_noW = S.maxH; free(hist); continue; }
        size_t hl = strlen(hist); char *h2 = malloc(hl + nord + 2); memcpy(h2, hist, hl); h2[hl] = ' '; memcpy(h2 + hl + 1, shape, nord + 1);
        if (hl == 0) memmove(h2, h2 + 1, nord + 1);
        free(hist);
        int isW = !strcmp(shape, "GWWW"), isX = !strcmp(shape, "GWWWW");
        if (S.g4 == 2 && !strcmp(shape, "GMB")) {          /* the stored G W W W was a phase-0 pass start */
            double tt; double sg = sigma_max(S.gB, S.gC, S.gW, &tt); long double w = 1.0L / (long double)((i128)1 << c.bits);
            int b = sg >= 1e8 ? NSB - 1 : (int)floor(sg); if (b < 0) b = 0; if (b >= NSB) b = NSB - 1;
            sig_mass[b] += w; sig_cnt[b]++; meas_entries += w; if (sg > sig_top) sig_top = sg;
            if (sg >= SIGPRINT) { printf("S %.3f t=%.3f bits %d coset %lld %lld %lld %lld %lld | %s\n", sg, tt, c.bits, c.x0[0], c.x0[1], c.B[0][0], c.B[1][0], c.B[1][1], h2); }
        }
        if (S.g4 == 1 && !strcmp(shape, "GBW")) S.g4 = 2; else S.g4 = 0;
        if (isW) {
            sortmarks();
            S.gB = S.P[order[2]]; S.gC = S.P[order[3]]; S.gW = S.W;
            S.g4 = 1;
        }
        if (isW) S.seenW = 1;
        if ((isW || isX) && getenv("RTPRINT")) {
            printf("%c %d %s |", isW ? 'W' : 'X', c.bits, h2);
            for (int i = 0; i < S.nout; i++) printf(" %d", S.outs[i]);
            printf("\n");
            if (isW) nW++; else nX++;
        }
        if (nd.rd + 1 >= MAXR) { lost += 1.0L / (long double)((i128)1 << c.bits); free(h2); continue; }
        if (top + 1 >= cap) { cap *= 2; stk = realloc(stk, sizeof(Node) * cap); hst = realloc(hst, sizeof(char *) * cap); }
        stk[top].st = S; stk[top].c = c; stk[top].nf = 0; stk[top].rd = nd.rd + 1; hst[top] = h2; top++;
    }
    fprintf(stderr, "cut %d part %d/%d: %lld G W W W prefixes, %lld G W W W W prefixes, lost %.4Le, dropped %lld\n", cut, part, nparts, nW, nX, lost, ndrop);
    fprintf(stderr, "phase-0 plain entries: measure %.6Le, largest sigma ceiling %.3f; measure by sigma ceiling (floor):", meas_entries, sig_top);
    for (int b = 0; b < NSB; b++) if (sig_cnt[b]) fprintf(stderr, " %d:%.4Le/%lld", b, sig_mass[b], sig_cnt[b]);
    fprintf(stderr, "\n");
    fprintf(stderr, "paths dropped: halted (packet reaches a block) %lld; bad by code:", nhalted); for (int b = 0; b < 16; b++) if (nbadp[b]) fprintf(stderr, " %d:%lld", b, nbadp[b]); fprintf(stderr, "\n");
    fprintf(stderr, "most halvings at an end meeting before any G W W W: %.2f (over complete segments that never reach G W W W: %.2f); in any run before it reaches G W W W: %.2f\n", Hmax_global, Hmax_noW, Hmax_run);
    return 0;
}
