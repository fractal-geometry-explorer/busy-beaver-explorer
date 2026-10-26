/* Depth-first version of the exhaustive class check (same model and the same tests as nrefdisk4.c, independent
   driver).  A class n = rho (mod 2^k), n = 2^k j + rho, keeps every position as a*j + b.  Instead of re-running each
   class's cycle from the clean tape at every level, the state at the start of the round where a test first needs
   digit k+1 is refined in place: with n = 2^(k+1) j' + rho', j = 2 j' + delta, so (a, b) -> (2a, a*delta + b).
   Open classes at level k get the direct run of n = rho + 2^k, as in nrefdisk.  Comparison thresholds are kept as a
   threshold on n, so j_min of a settled class is exact.  Separations are evaluated at the smallest member of the class
   current at the time of the probe, a lower bound for the settled class's (nrefdisk evaluates at the settled class).
   usage: nrefdfs K_max [part nparts split_level]   (covers every n < 2^(K_max + 1)) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long long ll; typedef __int128 i128;
typedef struct { ll a, b; } Q;
#define MAXM 256
/* ---- class context (used by comparisons) ---- */
static int CK; static ll CRHO;          /* current class: n = 2^CK j + CRHO */
static i128 NTHR;                        /* smallest n for which every comparison so far comes out as recorded */
static inline void need_j(ll jr) { i128 t = (i128)CRHO + ((i128)jr << CK); if (t > NTHR) NTHR = t; }
static inline int qcmp(Q x, Q y) {
    if (x.a != y.a) {
        ll d = y.a - x.a, D = y.b - x.b;
        ll t = d > 0 ? -D : D, ad = d > 0 ? d : -d;
        if (t >= 0) need_j(t / ad + 1);
        return x.a < y.a ? -1 : 1;
    }
    if (x.b != y.b) return x.b < y.b ? -1 : 1;
    return 0;
}
static inline Q qadd(Q x, ll c) { x.b += c; return x; }
typedef struct {
    int nm; Q W; int halted, bad, need;
    int haslast, lastr, chain, maxchain; Q lastd; int ff;
    char T[MAXM]; char A[MAXM]; Q P[MAXM];      /* arrays last: stcpy copies only the nm entries in use */
} St;
#include <stddef.h>
static inline void stcpy(St *d, const St *s) { memcpy(d, s, offsetof(St, T)); memcpy(d->T, s->T, s->nm); memcpy(d->A, s->A, s->nm); memcpy(d->P, s->P, s->nm * sizeof(Q)); }
static St S;
static ll minsep[3][4][4], minsep_n[3][4][4]; static ll PROBE_N;
static int LOGON = 0, NLOG = 0; static struct { short a, x, y; ll v, n; } ULOG[4096];   /* n at which probes are evaluated */
static int ti(char t) { return t == 'G' ? 0 : t == 'M' ? 1 : t == 'W' ? 2 : 3; }
static const int LENT[4] = {3, 2, 2, 3};
static int PROBE_ON = 1, FULLDIRECT = 0; static ll PJ;   /* probes evaluated at j = PJ of the current class */
static void probe(int phase) {
    if (!PROBE_ON) return;
    int idx[MAXM], k = 0;
    for (int i = 0; i < S.nm; i++) if (S.A[i]) idx[k++] = i;
    for (int i = 1; i < k; i++) { int v = idx[i], j = i - 1;
        while (j >= 0 && (S.P[idx[j]].a > S.P[v].a || (S.P[idx[j]].a == S.P[v].a && S.P[idx[j]].b > S.P[v].b))) { idx[j + 1] = idx[j]; j--; } idx[j + 1] = v; }
    for (int i = 0; i + 1 < k; i++) {
        int a = idx[i], b = idx[i + 1];
        ll sp = (S.P[b].a * PJ + S.P[b].b) - (S.P[a].a * PJ + S.P[a].b + LENT[ti(S.T[a])]);
        int x = ti(S.T[a]), y = ti(S.T[b]);
        if (sp < minsep[phase][x][y]) {
            if (LOGON && NLOG < 4096) { ULOG[NLOG].a = phase; ULOG[NLOG].x = x; ULOG[NLOG].y = y; ULOG[NLOG].v = minsep[phase][x][y]; ULOG[NLOG].n = minsep_n[phase][x][y]; NLOG++; }
            else if (LOGON) { fprintf(stderr, "undo log full\n"); exit(5); }
            minsep[phase][x][y] = sp; minsep_n[phase][x][y] = PROBE_N; }
    }
}
static void undo_log(void) { while (NLOG > 0) { NLOG--; minsep[ULOG[NLOG].a][ULOG[NLOG].x][ULOG[NLOG].y] = ULOG[NLOG].v; minsep_n[ULOG[NLOG].a][ULOG[NLOG].x][ULOG[NLOG].y] = ULOG[NLOG].n; } }
/* S.ff: no free slot below it (a hint, so the scan for a free slot is short) */
static int addm(char t, Q p) { for (int i = S.ff; i < S.nm; i++) if (!S.A[i]) { S.T[i] = t; S.P[i] = p; S.A[i] = 1; S.ff = i + 1; return i; }
    if (S.nm >= MAXM) { S.bad = 9; return 0; } S.T[S.nm] = t; S.P[S.nm] = p; S.A[S.nm] = 1; S.ff = S.nm + 1; return S.nm++; }
static inline void kill(int i) { S.A[i] = 0; if (i < S.ff) S.ff = i; }
static int first_right(Q x) { int b = -1; for (int i = 0; i < S.nm; i++) if (S.A[i] && qcmp(S.P[i], x) > 0 && (b < 0 || qcmp(S.P[i], S.P[b]) < 0)) b = i; return b; }
static int last_mark(void) { int b = -1; for (int i = 0; i < S.nm; i++) if (S.A[i] && (b < 0 || qcmp(S.P[i], S.P[b]) > 0)) b = i; return b; }
static int packet_back(Q x) {
    probe(2);
    int b = -1; for (int i = 0; i < S.nm; i++) if (S.A[i] && qcmp(S.P[i], x) < 0 && S.T[i] != 'M' && (b < 0 || qcmp(S.P[i], S.P[b]) > 0)) b = i;
    if (b < 0) return -1;
    if (S.T[b] == 'B') { S.halted = 1; return -1; }
    if (S.T[b] == 'G') { S.P[b].b += 2; return b; }
    Q q = S.P[b]; S.T[b] = 'M'; S.P[b] = qadd(q, -1); return addm('G', qadd(q, 1));
}
static int shift_from(Q x) {
    probe(1);
    int k = first_right(x);
    if (k < 0) { S.W.b += 2; addm('M', qadd(S.W, -2)); return packet_back(qadd(S.W, -2)); }
    if (S.T[k] == 'M') { S.T[k] = 'G'; return k; }
    if (S.T[k] == 'W') { S.T[k] = 'B'; return packet_back(S.P[k]); }
    if (S.T[k] == 'B') { S.T[k] = 'W'; S.P[k].b += 2; return packet_back(S.P[k]); }
    S.bad = 2; return -1;
}
static void end_meeting(Q d, int r4) {   /* incremental longest right-end chain, as chain_len() in nrefdisk */
    if (!S.haslast) { S.chain = 1; }
    else {
        Q p = S.lastr == 2 ? (Q){ S.lastd.a / 2, (S.lastd.b - 2) / 2 } : (Q){ S.lastd.a / 2, S.lastd.b / 2 + 4 };
        if (qcmp(d, p) == 0) S.chain++; else S.chain = 1;
    }
    if (S.chain > S.maxchain) S.maxchain = S.chain;
    S.haslast = 1; S.lastd = d; S.lastr = r4;
}
static void do_round(void) {
    int gap = -1; for (int i = 0; i < S.nm; i++) if (S.A[i] && S.T[i] == 'G' && qcmp(S.P[i], (Q){0, 1}) == 0) gap = i;
    while (gap >= 0 && !S.halted && !S.bad && !S.need) {
        probe(0);
        Q g = S.P[gap]; int m = first_right(g);
        if (m < 0) { kill(gap); S.W.b += 3; addm('M', qadd(S.W, -2)); gap = packet_back(qadd(S.W, -2)); continue; }
        if (S.T[m] == 'M') {
            Q d = { S.P[m].a - g.a, S.P[m].b - g.b - 3 };
            if (d.a % 4) { S.need = 1; return; }
            int r4 = (int)(((d.b % 4) + 4) % 4);
            if (d.a > 0 && d.b < 0) need_j((-d.b + d.a - 1) / d.a);
            if (d.a < 0 || (d.a == 0 && d.b < 0) || (r4 & 1)) { S.bad = 3; return; }
            if (m == last_mark()) end_meeting(d, r4);
            Q h = { d.a / 2, d.b / 2 };
            if (r4 == 0) { S.P[m] = (Q){ g.a + h.a, g.b + h.b - 1 }; S.P[gap] = (Q){ g.a + h.a, g.b + h.b + 1 }; }
            else { kill(gap); S.T[m] = 'W'; S.P[m] = (Q){ g.a + h.a, g.b + h.b + 3 }; gap = packet_back(S.P[m]); }
        } else if (S.T[m] == 'W') { Q x = S.P[m]; kill(gap); kill(m); gap = shift_from(x); }
        else if (S.T[m] == 'B') { S.T[m] = 'W'; S.P[m].b -= 1; gap = shift_from(S.P[m]); }
        else { S.bad = 4; return; }
    }
    if (S.halted || S.bad || S.need) return;
    ll extra = 2;
    for (int i = 0; i < S.nm; i++) if (S.A[i] && S.T[i] == 'M' && qcmp(S.P[i], (Q){0, 0}) == 0) { S.T[i] = 'W'; S.P[i].b = 1; extra = 4; }
    for (int i = 0; i < S.nm; i++) if (S.A[i]) S.P[i].b += extra;
    S.W.b += extra; addm('G', (Q){0, 1});
}
static int at_clean(void) {
    int alive = 0, ok = 0; Q e = qadd(S.W, -2);
    for (int i = 0; i < S.nm; i++) if (S.A[i]) { alive++; if (S.T[i] == 'M' && qcmp(S.P[i], e) == 0) ok = 1; }
    return alive == 2 && ok;
}
/* direct run of one integer n (all positions constant), as cycle_int */
static int cycle_int(ll n, ll *jump, int *chain) {
    int sk = CK; ll sr = CRHO; i128 st = NTHR; ll spj = PJ, spn = PROBE_N;
    CK = 0; CRHO = 0; NTHR = 0; PJ = 0; PROBE_N = n;
    memset(&S, 0, sizeof S); S.W = (Q){ 0, 2 * n + 6 };
    addm('G', (Q){0, 1}); addm('M', qadd(S.W, -2));
    int res = 4;
    for (int r = 1; r <= 20000; r++) {
        do_round();
        if (S.need) { res = 1; break; } if (S.halted) { res = 2; break; } if (S.bad) { res = 3; break; }
        if (at_clean()) { *jump = (S.W.b - (2 * n + 6)) / 2; *chain = S.maxchain; res = 0; break; }
    }
    CK = sk; CRHO = sr; NTHR = st; PJ = spj; PROBE_N = spn;
    return res;
}
/* the same direct run, started from a symbolic state at the start of a round, evaluated at j (valid when every
   comparison made before that round holds at j) */
static int cycle_from(const St *st, ll j, ll n, ll *jump, int *chain) {
    int sk = CK; ll sr = CRHO; i128 stt = NTHR; ll spj = PJ, spn = PROBE_N;
    CK = 0; CRHO = 0; NTHR = 0; PJ = 0; PROBE_N = n;
    stcpy(&S, st);
    for (int i = 0; i < S.nm; i++) S.P[i] = (Q){ 0, S.P[i].a * j + S.P[i].b };
    S.W = (Q){ 0, S.W.a * j + S.W.b }; if (S.haslast) S.lastd = (Q){ 0, S.lastd.a * j + S.lastd.b };
    int res = 4;
    for (int r = 1; r <= 20000; r++) {
        do_round();
        if (S.need) { res = 1; break; } if (S.halted) { res = 2; break; } if (S.bad) { res = 3; break; }
        if (at_clean()) { *jump = (S.W.b - (2 * n + 6)) / 2; *chain = S.maxchain; res = 0; break; }
    }
    CK = sk; CRHO = sr; NTHR = stt; PJ = spj; PROBE_N = spn;
    return res;
}
typedef struct { St st; int k; ll rho; i128 nthr; int rounds; } Node;
static long long settled[64], openc[64], direct[64], dbad[64], cbad[64], chainh[64], jminmax[64], jmin_rho[64];
static int maxchain_lvl[64], dmax_lvl[64]; static ll dmax_n[64], Jmax = 0, Jmax_n = 0;
static void refine(St *s, ll delta) {     /* (a, b) -> (2a, a*delta + b) for every position */
    for (int i = 0; i < s->nm; i++) { Q p = s->P[i]; s->P[i] = (Q){ 2 * p.a, p.a * delta + p.b }; }
    Q w = s->W; s->W = (Q){ 2 * w.a, w.a * delta + w.b };
    if (s->haslast) { Q d = s->lastd; s->lastd = (Q){ 2 * d.a, d.a * delta + d.b }; }
}
int main(int argc, char **argv) {
    int K = atoi(argv[1]); int part = argc > 2 ? atoi(argv[2]) : 0, nparts = argc > 3 ? atoi(argv[3]) : 1;
    int splitlvl = argc > 4 ? atoi(argv[4]) : 12; if (getenv("FULLDIRECT")) FULLDIRECT = 1;
    for (int a = 0; a < 3; a++) for (int x = 0; x < 4; x++) for (int y = 0; y < 4; y++) minsep[a][x][y] = 1LL << 62;
    int cap = 1 << 10, top = 0; Node *stk = malloc(sizeof(Node) * cap);
    /* the root: level 1 classes rho = 0, 1 (mod 2), clean tape W = 2n + 6 = 2(2j + rho) + 6 */
    for (ll rho = 1; rho >= 0; rho--) {
        Node nd; memset(&nd, 0, sizeof nd); nd.k = 1; nd.rho = rho; nd.nthr = 0; nd.rounds = 0;
        memset(&S, 0, sizeof S); S.W = (Q){ 4, 2 * rho + 6 }; addm('G', (Q){0, 1}); addm('M', qadd(S.W, -2));
        nd.st = S; stk[top++] = nd;
    }
    while (top > 0) {
        top--; Node nd; { Node *np = &stk[top]; nd.k = np->k; nd.rho = np->rho; nd.nthr = np->nthr; nd.rounds = np->rounds; stcpy(&S, &np->st); }
         CK = nd.k; CRHO = nd.rho; NTHR = nd.nthr; PJ = 1; PROBE_N = nd.rho + (1LL << nd.k);
        static St start; int rounds = nd.rounds, outcome = -1;
        for (;;) {
            stcpy(&start, &S); i128 nthr0 = NTHR;
            LOGON = 1; NLOG = 0; do_round(); LOGON = 0; rounds++;
            int own = nparts == 1 || nd.k >= splitlvl || part == 0;
            if (S.need) {
                undo_log();
                int k = nd.k;
                ll n = nd.rho + (1LL << k), dj = 0; int dc = 0, ds = 0;
                if (own) { openc[k]++; ds = (nthr0 <= (i128)n && !FULLDIRECT) ? cycle_from(&start, 1, n, &dj, &dc) : cycle_int(n, &dj, &dc); direct[k]++; }
                if (ds != 0) { dbad[k]++; printf("  DIRECT n = %lld: %s\n", n, ds == 2 ? "HALTS" : ds == 3 ? "bad" : "too long"); fflush(stdout); }
                else { if (dc > dmax_lvl[k]) { dmax_lvl[k] = dc; dmax_n[k] = n; } if (dj > Jmax) { Jmax = dj; Jmax_n = n; } }
                if (k < K) for (int delta = 1; delta >= 0; delta--) {
                    ll r2 = nd.rho + delta * (1LL << k);
                    if (nparts > 1 && k + 1 == splitlvl && (int)((((unsigned long long)r2 * 2654435761ULL) >> 16) % nparts) != part) continue;
                    if (top + 1 >= cap) { cap *= 2; stk = realloc(stk, sizeof(Node) * cap); }
                    Node *c = &stk[top++]; c->k = k + 1; c->rho = r2; stcpy(&c->st, &start); refine(&c->st, delta); c->nthr = nthr0; c->rounds = rounds - 1;
                }
                outcome = 1; break;
            }
            if (S.halted || S.bad) { cbad[nd.k]++; printf("  class n = %lld (mod 2^%d): %s\n", nd.rho, nd.k, S.halted ? "HALTS" : "contact/bad"); fflush(stdout); outcome = 2; break; }
            if (at_clean()) {
                int k = nd.k; if (!own) { outcome = 0; break; } settled[k]++;
                ll jump = (S.W.b - (2 * nd.rho + 6)) / 2;
                i128 t = NTHR - nd.rho; ll jmin = 0; if (t > 0) { i128 q = t >> k; if ((q << k) < t) q++; jmin = (ll)q; }
                if (jmin > jminmax[k]) { jminmax[k] = jmin; jmin_rho[k] = nd.rho; }
                if (jmin >= 2) { fprintf(stderr, "%d %lld %lld %lld %d\n", k, nd.rho, jmin, jump, S.maxchain); }
                int ch = S.maxchain > 63 ? 63 : S.maxchain; chainh[ch]++; if (ch > maxchain_lvl[k]) maxchain_lvl[k] = ch;
                if (jump > Jmax) { Jmax = jump; Jmax_n = nd.rho + (1LL << k); }
                if (ch >= 13) { printf("  chain %d: n = %lld (mod 2^%d), jump %lld\n", ch, nd.rho, k, jump); fflush(stdout); }
                outcome = 0; break;
            }
            if (rounds >= 20000) { cbad[nd.k]++; printf("  class n = %lld (mod 2^%d): too long\n", nd.rho, nd.k); outcome = 3; break; }
        }
        (void)outcome;
    }
    long long ts = 0, td = 0, tb = 0; int oc = 0; ll jm = 0;
    for (int k = 1; k <= K; k++) {
        ts += settled[k]; td += direct[k]; tb += dbad[k] + cbad[k]; if (maxchain_lvl[k] > oc) oc = maxchain_lvl[k]; if (jminmax[k] > jm) jm = jminmax[k];
        printf("digits %2d: settled %lld, still open %lld, longest chain here %d (overall %d), largest j_min %lld, direct runs %lld (problems %lld, longest chain %d at n = %lld), class problems %lld\n",
               k, settled[k], openc[k], maxchain_lvl[k], oc, jminmax[k], direct[k], dbad[k], dmax_lvl[k], dmax_n[k], cbad[k]);
    }
    { const char *ph[3] = {"gap", "shift", "packet"}, *nmT = "GMWB"; printf("closest approaches (lower bounds):\n");
      for (int a = 0; a < 3; a++) for (int x = 0; x < 4; x++) for (int y = 0; y < 4; y++)
        if (minsep[a][x][y] < (1LL << 62)) printf("  %s %c%c min %lld (n=%lld)\n", ph[a], nmT[x], nmT[y], minsep[a][x][y], minsep_n[a][x][y]); }
    printf("totals: settled classes %lld, direct runs %lld, problems %lld, largest j_min %lld, largest jump %lld (n = %lld), longest chain %d\n", ts, td, tb, jm, Jmax, Jmax_n, oc);
    return 0;
}
