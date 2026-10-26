/* rline: the same exact tree for ONE SEGMENT of a line of GMM states, m = m0 + am*t, E = E0 + aE*t (t free), up to
   the next GMM state or the clean tape.  Tail P(h >= x) with h = log2(E/d) at the closest end meeting, t -> infinity.
   usage: rline cut am m0 aE E0      (am, m0, aE even, E0 odd, 0 < am < aE)
   Derived from: Exact 2-adic tree of whole cycles from even clean tapes n (one free number): the cycle starts at the GMM state
   m = n + 2, E = 2n + 11, every position is a form (a n + c) / 2^e, order is taken as n -> infinity, and every d mod 4
   test either is decided on the current class of n or splits it.  The class is followed through all its segments
   until the clean tape.  For each completed class: its closest right-end meeting in halvings log2(E/d) as n -> inf,
   accumulated into a tail P(h >= x) over even n; also the jump n' - n.
   usage: rtree1d cut_bits [maxrounds] */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <setjmp.h>
static jmp_buf JB;
typedef long long ll; typedef __int128 i128;
#define MAXM 64
#define MAXO 6000
typedef struct { ll a, c; int e; } Form;          /* (a n + c) / 2^e */
static Form norm(Form f) { while (f.e > 0 && !((f.a | f.c) & 1)) { f.a /= 2; f.c /= 2; f.e--; } return f; }
static Form fconst(ll k) { Form f = {0, k, 0}; return f; }
static Form fadd(Form f, ll k) { if (f.e > 55) { longjmp(JB, 1); } f.c += k * (1LL << f.e); return f; }
static Form fplus(Form p, Form q, int sgn) {
    int e = p.e > q.e ? p.e : q.e; Form r;
    if (e > 60) longjmp(JB, 1);
    ll sp = 1LL << (e - p.e), sq = 1LL << (e - q.e), x1, x2, x3, x4;
    if (__builtin_mul_overflow(p.a, sp, &x1) || __builtin_mul_overflow(q.a, sq, &x2) || __builtin_mul_overflow(p.c, sp, &x3) || __builtin_mul_overflow(q.c, sq, &x4)
        || __builtin_add_overflow(x1, sgn * x2, &r.a) || __builtin_add_overflow(x3, sgn * x4, &r.c)) { longjmp(JB, 1); }
    r.e = e; return norm(r);
}
static Form fhalf(Form f) { f.e++; return norm(f); }
static int fcmp(Form p, Form q) {
    int e = p.e > q.e ? p.e : q.e; i128 sp = (i128)1 << (e - p.e), sq = (i128)1 << (e - q.e);
    i128 k1 = (i128)p.a * sp, k2 = (i128)q.a * sq;
    if (k1 != k2) return k1 < k2 ? -1 : 1;
    k1 = (i128)p.c * sp; k2 = (i128)q.c * sq;
    if (k1 != k2) return k1 < k2 ? -1 : 1;
    return 0;
}
static int fcmpk(Form p, ll k) { return fcmp(p, fconst(k)); }
typedef struct { ll x0, B; int bits; } Coset;       /* n = x0 + B y */
static int cerr;
static int evalf(const Coset *C, Form f, i128 *f0, i128 *g) {
    i128 a0 = (i128)f.c + (i128)f.a * C->x0, g0 = (i128)f.a * C->B, den = (i128)1 << f.e;
    if ((a0 % den) || (g0 % den)) { cerr = 1; return 0; }
    *f0 = a0 / den; *g = g0 / den; return 1;
}
static int decided(const Coset *C, Form f) {
    i128 f0, g; if (!evalf(C, f, &f0, &g)) return -2;
    if (((g >> 1) & 1) == 0) { int r = (int)(f0 % 4); if (r < 0) r += 4; return r; }
    return -1;
}
static void impose(Coset *C, Form f, int res) {
    i128 f0, g; if (!evalf(C, f, &f0, &g)) return;
    if ((f0 & 1) || (g & 1)) { cerr = 1; return; }
    i128 h = g / 2; if (!(h & 1)) return;
    i128 tt = (res - f0) / 2; int t = (int)(tt % 2); if (t < 0) t += 2;
    C->x0 += (ll)t * C->B; C->B *= 2; C->bits++;
    if (C->B > (1LL << 61)) longjmp(JB, 1);
    /* reduce x0 mod B */
    C->x0 %= C->B; if (C->x0 < 0) C->x0 += C->B;
}
typedef struct {
    char T[MAXM]; Form P[MAXM]; char A[MAXM]; int nm; Form W; int halted, bad; int nout; double U[30]; double hmax;
} St;
static St S; static Coset *CC; static const unsigned char *FRC; static int NFRC, FI, BRANCH;
static int addm(char t, Form p) {
    for (int i = 0; i < S.nm; i++) if (!S.A[i]) { S.T[i] = t; S.P[i] = p; S.A[i] = 1; return i; }
    if (S.nm >= MAXM) { S.bad = 9; return 0; }
    S.T[S.nm] = t; S.P[S.nm] = p; S.A[S.nm] = 1; return S.nm++;
}
static int first_right(Form x) { int b = -1; for (int i = 0; i < S.nm; i++) if (S.A[i] && fcmp(S.P[i], x) > 0 && (b < 0 || fcmp(S.P[i], S.P[b]) < 0)) b = i; return b; }
static int last_mark(void) { int b = -1; for (int i = 0; i < S.nm; i++) if (S.A[i] && (b < 0 || fcmp(S.P[i], S.P[b]) > 0)) b = i; return b; }
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
static ll AE;
static double HMAX;
static void meet_end(Form d) {      /* closest approach bookkeeping: h = log2(E/d), E ~ aE t */
    if (d.a <= 0) { for (int x = 0; x < 30; x++) S.U[x] = 1; return; }
    double h = d.e + log2((double)AE) - log2((double)d.a); if (h > S.hmax) S.hmax = h;
    for (int x = 0; x < 30; x++) if (h >= x) S.U[x] = 1;
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
            if (res < 0) return;
            S.nout++;
            if (islast) meet_end(d);
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
typedef struct { St st; Coset c; unsigned char forced[64]; int nf; int rd; } Node;
static Node *STK; static int CAP;
/* one line: reach (largest closest-approach h over completed classes), the class that attains it, undecided measure */
static int run_line(int cut, ll am, ll m0, ll aE, ll E0, double *reach, ll *bx0, int *bbits, long double *lostp, long double *t12) {
    int maxr = 3000, top = 0; AE = aE;
    memset(&S, 0, sizeof S); S.hmax = -99;
    Form Wf = {aE, E0, 0}; S.W = Wf;
    addm('G', fconst(1)); Form mf = {am, m0, 0}; addm('M', mf); addm('M', fadd(S.W, -2));
    Node n0; memset(&n0, 0, sizeof n0); n0.st = S; n0.c.x0 = 0; n0.c.B = 1; n0.c.bits = 0; n0.nf = 0; n0.rd = 0;
    STK[top++] = n0;
    long double lost = 0, tt = 0; *reach = -99; *bx0 = 0; *bbits = 0;
    while (top > 0) {
        Node nd = STK[--top];
        S = nd.st; Coset c = nd.c; CC = &c; FRC = nd.forced; NFRC = nd.nf; FI = 0; BRANCH = 0; cerr = 0;
        do_round();
        if (BRANCH) {
            int nb = nd.c.bits + nd.nf + 1;
            if (nb > cut) { lost += 1.0L / (long double)((i128)1 << (nd.c.bits + nd.nf)); continue; }
            for (int oi = 0; oi < 2; oi++) {
                if (top + 1 >= CAP) { CAP *= 2; STK = realloc(STK, sizeof(Node) * CAP); }
                STK[top] = nd; STK[top].forced[nd.nf] = (unsigned char)(oi ? 0 : 2); STK[top].nf = nd.nf + 1; top++;
            }
            continue;
        }
        if (cerr) continue;
        if (S.halted || S.bad) { printf("HALTBAD %lld %lld %lld %lld x0 %lld B %lld\n", am, m0, aE, E0, c.x0, c.B); continue; }
        int na = 0, ng = 0, nmk = 0, endok = 0; Form e2 = fadd(S.W, -2);
        for (int i = 0; i < S.nm; i++) if (S.A[i]) { na++; if (S.T[i] == 'G' && fcmpk(S.P[i], 1) == 0) ng++; else if (S.T[i] == 'M') { nmk++; if (fcmp(S.P[i], e2) == 0) endok = 1; } }
        if (endok && ng == 1 && ((na == 2 && nmk == 1) || (na == 3 && nmk == 2)) && S.nout > 0) {
            if (S.hmax > *reach) { *reach = S.hmax; *bx0 = c.x0; *bbits = c.bits; }
            if (S.hmax >= 12) tt += 1.0L / (long double)((i128)1 << c.bits);
            continue;
        }
        if (nd.rd + 1 >= maxr) { lost += 1.0L / (long double)((i128)1 << c.bits); continue; }
        if (top + 1 >= CAP) { CAP *= 2; STK = realloc(STK, sizeof(Node) * CAP); }
        STK[top].st = S; STK[top].c = c; STK[top].nf = 0; STK[top].rd = nd.rd + 1; top++;
    }
    *lostp = lost; *t12 = tt; return 0;
}
int main(int argc, char **argv) {
    int cut = atoi(argv[1]); CAP = 1 << 12; STK = malloc(sizeof(Node) * CAP);
    int bits; ll am, m0, aE, E0, rd; char tag[8];
    while (scanf("%7s %d %lld %lld %lld %lld %lld", tag, &bits, &am, &m0, &aE, &E0, &rd) == 7) {
        double reach; ll bx0; int bb; long double lost, t12;
        if (setjmp(JB)) { printf("R %d %lld %lld %lld %lld OVERFLOW\n", bits, am, m0, aE, E0); fflush(stdout); continue; }
        run_line(cut, am, m0, aE, E0, &reach, &bx0, &bb, &lost, &t12);
        printf("R %d %lld %lld %lld %lld reach %.4f best_x0 %lld best_bits %d undecided %.3Le t12 %.3Le\n", bits, am, m0, aE, E0, reach, bx0, bb, lost, t12);
        fflush(stdout);
    }
    return 0;
}
