/* nrefdfs2: nrefdfs (depth-first exhaustive class check) with the marks kept in a sorted doubly linked list.
   Same model, same tests, same driver.  Differences from nrefdfs:
   - "first mark to the right", "last mark", "nearest non-marker to the left" are list neighbours, not scans;
   - an order comparison (with its threshold on n) is made for every pair of marks that becomes adjacent or changes
     position, which is exactly what the order of the list needs to hold for n >= threshold.  (nrefdisk/nrefdfs also
     compare non-adjacent pairs while scanning; those thresholds are implied by the adjacent ones, so j_min here can
     only be smaller or equal, and stays a valid guarantee.)
   - separations are probed only for pairs that changed since the last probe of the same phase (the others have the
     value they had then), so the minima are the same as probing every pair at every probe.
   usage: nrefdfs2 K_max [part nparts split_level] */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stddef.h>
#include <math.h>
typedef long long ll; typedef __int128 i128;
typedef struct { ll a, b; } Q;
#define MAXM 256
static int CK; static ll CRHO; static i128 NTHR;
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
    int haslast, lastr, chain, maxchain; Q lastd; int ff; double maxh;
    int head, tail, alive;
    char T[MAXM]; char A[MAXM]; short nx[MAXM], pv[MAXM]; Q P[MAXM];
} St;
static inline void stcpy(St *d, const St *s) {
    memcpy(d, s, offsetof(St, T)); int n = s->nm;
    memcpy(d->T, s->T, n); memcpy(d->A, s->A, n); memcpy(d->nx, s->nx, n * sizeof(short)); memcpy(d->pv, s->pv, n * sizeof(short)); memcpy(d->P, s->P, n * sizeof(Q));
}
static St S;
/* ---- probes ---- */
static ll minsep[3][4][4], minsep_n[3][4][4]; static ll PROBE_N, PJ;
static int LOGON = 0, NLOG = 0; static struct { short a, x, y; ll v, n; } ULOG[4096];
static const int TI[128] = { ['G'] = 0, ['M'] = 1, ['W'] = 2, ['B'] = 3 };
static const int LENT[4] = {3, 2, 2, 3};
static unsigned char DM[MAXM]; static short DL[4 * MAXM]; static int NDL = 0, ALLD = 7;
static inline void dirty(int i) { if (i < 0) return; if (!DM[i]) { if (NDL >= 4 * MAXM) { ALLD = 7; NDL = 0; memset(DM, 0, sizeof DM); return; } DL[NDL++] = i; } DM[i] = 7; }
static inline void evpair(int phase, int u, int v) {
    ll sp = (S.P[v].a * PJ + S.P[v].b) - (S.P[u].a * PJ + S.P[u].b + LENT[TI[(int)S.T[u]]]);
    int x = TI[(int)S.T[u]], y = TI[(int)S.T[v]];
    if (sp < minsep[phase][x][y]) {
        if (LOGON) { if (NLOG >= 4096) { fprintf(stderr, "undo log full\n"); exit(5); }
            ULOG[NLOG].a = phase; ULOG[NLOG].x = x; ULOG[NLOG].y = y; ULOG[NLOG].v = minsep[phase][x][y]; ULOG[NLOG].n = minsep_n[phase][x][y]; NLOG++; }
        minsep[phase][x][y] = sp; minsep_n[phase][x][y] = PROBE_N;
    }
}
static void probe(int phase) {
    int bit = 1 << phase;
    if (ALLD & bit) {
        for (int i = S.head; i >= 0 && S.nx[i] >= 0; i = S.nx[i]) evpair(phase, i, S.nx[i]);
        ALLD &= ~bit; for (int t = 0; t < NDL; t++) DM[DL[t]] &= ~bit;
    } else {
        for (int t = 0; t < NDL; t++) { int i = DL[t]; if (!(DM[i] & bit)) continue; DM[i] &= ~bit;
            if (!S.A[i]) continue;
            if (S.pv[i] >= 0 && !(DM[S.pv[i]] & bit)) evpair(phase, S.pv[i], i);   /* (if pv is dirty too, it evaluates this pair) */
            else if (S.pv[i] >= 0) evpair(phase, S.pv[i], i);
            if (S.nx[i] >= 0) evpair(phase, i, S.nx[i]); }
    }
    int w = 0; for (int t = 0; t < NDL; t++) if (DM[DL[t]]) DL[w++] = DL[t]; NDL = w;
}
static void undo_log(void) { while (NLOG > 0) { NLOG--; minsep[ULOG[NLOG].a][ULOG[NLOG].x][ULOG[NLOG].y] = ULOG[NLOG].v; minsep_n[ULOG[NLOG].a][ULOG[NLOG].x][ULOG[NLOG].y] = ULOG[NLOG].n; } }
static void reset_probes(void) { ALLD = 7; for (int t = 0; t < NDL; t++) DM[DL[t]] = 0; NDL = 0; }
/* ---- the sorted list ---- */
static int newslot(char t, Q p) {
    int i = -1; for (int k = S.ff; k < S.nm; k++) if (!S.A[k]) { i = k; break; }
    if (i < 0) { if (S.nm >= MAXM) { S.bad = 9; return -1; } i = S.nm++; }
    S.ff = i + 1; S.T[i] = t; S.P[i] = p; S.A[i] = 1; S.alive++; S.nx[i] = S.pv[i] = -1; dirty(i); return i;
}
static inline void unlink_(int i) {
    int p = S.pv[i], n = S.nx[i];
    if (p >= 0) S.nx[p] = n; else S.head = n;
    if (n >= 0) S.pv[n] = p; else S.tail = p;
}
static inline void link_after(int i, int p) {      /* p = -1: at the head */
    int n = p >= 0 ? S.nx[p] : S.head;
    S.pv[i] = p; S.nx[i] = n;
    if (p >= 0) S.nx[p] = i; else S.head = i;
    if (n >= 0) S.pv[n] = i; else S.tail = i;
}
static void killm(int i) { int p = S.pv[i], n = S.nx[i]; unlink_(i); S.A[i] = 0; S.alive--; if (i < S.ff) S.ff = i; dirty(p); dirty(n); }
/* put mark i (already linked somewhere near its place) where its position belongs, comparing it with every mark it
   passes and with its final neighbours (each comparison records its threshold on n) */
static void fix(int i) {
    dirty(i);
    for (;;) { int p = S.pv[i]; if (p < 0) break; int c = qcmp(S.P[p], S.P[i]); if (c == 0) { S.bad = 8; return; } if (c < 0) break;
        unlink_(i); link_after(i, S.pv[p]); dirty(p); }
    for (;;) { int n = S.nx[i]; if (n < 0) break; int c = qcmp(S.P[i], S.P[n]); if (c == 0) { S.bad = 8; return; } if (c < 0) break;
        unlink_(i); link_after(i, n); dirty(n); }
    dirty(S.pv[i]); dirty(S.nx[i]);
}
static int addm_after(char t, Q p, int after) { int i = newslot(t, p); if (i < 0) return -1; link_after(i, after); fix(i); return i; }
/* ---- the rules (same as nrefdisk/nrefdfs) ---- */
static int packet_back_from(int k) {          /* k: the mark whose position x the packet starts from (strictly left of it) */
    probe(2);
    int b = S.pv[k]; while (b >= 0 && S.T[b] == 'M') b = S.pv[b];
    if (b < 0) return -1;
    if (S.T[b] == 'B') { S.halted = 1; return -1; }
    if (S.T[b] == 'G') { S.P[b].b += 2; fix(b); return b; }
    Q q = S.P[b]; S.T[b] = 'M'; S.P[b] = qadd(q, -1); fix(b);
    return addm_after('G', qadd(q, 1), b);
}
static int shift_from_succ(int k) {          /* k: the first mark to the right of the shift's start (or -1) */
    probe(1);
    if (k < 0) { S.W.b += 2; int e = addm_after('M', qadd(S.W, -2), S.tail); if (e < 0) return -1; return packet_back_from(e); }
    if (S.T[k] == 'M') { S.T[k] = 'G'; dirty(k); return k; }
    if (S.T[k] == 'W') { S.T[k] = 'B'; dirty(k); return packet_back_from(k); }
    if (S.T[k] == 'B') { S.T[k] = 'W'; S.P[k].b += 2; fix(k); return packet_back_from(k); }
    S.bad = 2; return -1;
}
static void end_meeting(Q d, int r4) {
    if (!S.haslast) S.chain = 1;
    else { Q p = S.lastr == 2 ? (Q){ S.lastd.a / 2, (S.lastd.b - 2) / 2 } : (Q){ S.lastd.a / 2, S.lastd.b / 2 + 4 };
        if (qcmp(d, p) == 0) S.chain++; else S.chain = 1; }
    if (S.chain > S.maxchain) S.maxchain = S.chain;
    S.haslast = 1; S.lastd = d; S.lastr = r4;
}
static void do_round(void) {
    int gap = S.head;
    if (gap >= 0 && !(S.T[gap] == 'G' && qcmp(S.P[gap], (Q){0, 1}) == 0)) gap = -1;
    while (gap >= 0 && !S.halted && !S.bad && !S.need) {
        probe(0);
        int m = S.nx[gap];
        if (m < 0) { killm(gap); S.W.b += 3; int e = addm_after('M', qadd(S.W, -2), S.tail); if (e < 0) return; gap = packet_back_from(e); continue; }
        if (S.T[m] == 'M') {
            Q g = S.P[gap]; Q d = { S.P[m].a - g.a, S.P[m].b - g.b - 3 };
            if (d.a % 4) { S.need = 1; return; }
            int r4 = (int)(((d.b % 4) + 4) % 4);
            if (d.a > 0 && d.b < 0) need_j((-d.b + d.a - 1) / d.a);
            if (d.a < 0 || (d.a == 0 && d.b < 0) || (r4 & 1)) { S.bad = 3; return; }
            if (m == S.tail) { end_meeting(d, r4);
                if (CK > 0) { double hv = d.a > 0 ? CK + 1 - log2((double)d.a) : 99.0; if (hv > S.maxh) S.maxh = hv; } }
            Q h = { d.a / 2, d.b / 2 };
            if (r4 == 0) { S.P[m] = (Q){ g.a + h.a, g.b + h.b - 1 }; S.P[gap] = (Q){ g.a + h.a, g.b + h.b + 1 }; fix(gap); fix(m); }
            else { killm(gap); S.T[m] = 'W'; S.P[m] = (Q){ g.a + h.a, g.b + h.b + 3 }; fix(m); gap = packet_back_from(m); }
        } else if (S.T[m] == 'W') { int s = S.nx[m]; killm(gap); killm(m); gap = shift_from_succ(s); }
        else if (S.T[m] == 'B') { S.T[m] = 'W'; S.P[m].b -= 1; fix(m); gap = shift_from_succ(S.nx[m]); }
        else { S.bad = 4; return; }
    }
    if (S.halted || S.bad || S.need) return;
    ll extra = 2; int h0 = S.head;
    if (h0 >= 0 && S.T[h0] == 'M' && qcmp(S.P[h0], (Q){0, 0}) == 0) { S.T[h0] = 'W'; S.P[h0].b = 1; extra = 4; fix(h0); }
    for (int i = S.head; i >= 0; i = S.nx[i]) S.P[i].b += extra;
    S.W.b += extra; addm_after('G', (Q){0, 1}, -1);
}
static int at_clean(void) { return S.alive == 2 && S.tail >= 0 && S.T[S.tail] == 'M' && qcmp(S.P[S.tail], qadd(S.W, -2)) == 0; }
static void init_state(Q W) {
    memset(&S, 0, offsetof(St, T)); S.head = S.tail = -1; S.W = W;
    addm_after('G', (Q){0, 1}, -1); addm_after('M', qadd(S.W, -2), S.tail);
}
static int run_rounds(ll n, ll *jump, int *chain) {
    int res = 4;
    for (int r = 1; r <= 20000; r++) {
        do_round();
        if (S.need) { res = 1; break; } if (S.halted) { res = 2; break; } if (S.bad) { res = 3; break; }
        if (at_clean()) { *jump = (S.W.b - (2 * n + 6)) / 2; *chain = S.maxchain; res = 0; break; }
    }
    return res;
}
static int cycle_int(ll n, ll *jump, int *chain) {
    int sk = CK; ll sr = CRHO; i128 st = NTHR; ll spj = PJ, spn = PROBE_N;
    CK = 0; CRHO = 0; NTHR = 0; PJ = 0; PROBE_N = n; reset_probes();
    init_state((Q){ 0, 2 * n + 6 });
    int res = run_rounds(n, jump, chain);
    CK = sk; CRHO = sr; NTHR = st; PJ = spj; PROBE_N = spn;
    return res;
}
static int cycle_from(const St *st, ll j, ll n, ll *jump, int *chain) {
    int sk = CK; ll sr = CRHO; i128 stt = NTHR; ll spj = PJ, spn = PROBE_N;
    CK = 0; CRHO = 0; NTHR = 0; PJ = 0; PROBE_N = n; reset_probes();
    stcpy(&S, st);
    for (int i = 0; i < S.nm; i++) S.P[i] = (Q){ 0, S.P[i].a * j + S.P[i].b };
    S.W = (Q){ 0, S.W.a * j + S.W.b }; if (S.haslast) S.lastd = (Q){ 0, S.lastd.a * j + S.lastd.b };
    int res = run_rounds(n, jump, chain);
    CK = sk; CRHO = sr; NTHR = stt; PJ = spj; PROBE_N = spn;
    return res;
}
typedef struct { St st; int k; ll rho; i128 nthr; int rounds; } Node;
static long long settled[64], openc[64], direct[64], dbad[64], cbad[64], chainh[64], jminmax[64], jmin_rho[64];
static long double TAILB[640]; static int maxchain_lvl[64], dmax_lvl[64]; static ll dmax_n[64], Jmax = 0, Jmax_n = 0;
static void refine(St *s, ll delta) {
    for (int i = 0; i < s->nm; i++) { Q p = s->P[i]; s->P[i] = (Q){ 2 * p.a, p.a * delta + p.b }; }
    Q w = s->W; s->W = (Q){ 2 * w.a, w.a * delta + w.b };
    if (s->haslast) { Q d = s->lastd; s->lastd = (Q){ 2 * d.a, d.a * delta + d.b }; }
}
int main(int argc, char **argv) {
    int K = atoi(argv[1]); int part = argc > 2 ? atoi(argv[2]) : 0, nparts = argc > 3 ? atoi(argv[3]) : 1;
    int splitlvl = argc > 4 ? atoi(argv[4]) : 12;
    for (int a = 0; a < 3; a++) for (int x = 0; x < 4; x++) for (int y = 0; y < 4; y++) minsep[a][x][y] = 1LL << 62;
    int cap = 1 << 10, top = 0; Node *stk = malloc(sizeof(Node) * cap);
    for (ll rho = 1; rho >= 0; rho--) {
        Node *nd = &stk[top++]; nd->k = 1; nd->rho = rho; nd->nthr = 0; nd->rounds = 0;
        CK = 1; CRHO = rho; NTHR = 0; PJ = 1; PROBE_N = rho + 2;
        init_state((Q){ 4, 2 * rho + 6 }); stcpy(&nd->st, &S);
    }
    static St start;
    while (top > 0) {
        top--; Node nd; { Node *np = &stk[top]; nd.k = np->k; nd.rho = np->rho; nd.nthr = np->nthr; nd.rounds = np->rounds; stcpy(&S, &np->st); }
        CK = nd.k; CRHO = nd.rho; NTHR = nd.nthr; PJ = 1; PROBE_N = nd.rho + (1LL << nd.k); reset_probes();
        int rounds = nd.rounds;
        for (;;) {
            stcpy(&start, &S); i128 nthr0 = NTHR;
            LOGON = 1; NLOG = 0; do_round(); LOGON = 0; rounds++;
            int own = nparts == 1 || nd.k >= splitlvl || part == 0;
            if (S.need) {
                undo_log();
                int k = nd.k;
                ll n = nd.rho + (1LL << k), dj = 0; int dc = 0, ds = 0;
                if (own) { openc[k]++; ds = nthr0 <= (i128)n ? cycle_from(&start, 1, n, &dj, &dc) : cycle_int(n, &dj, &dc); direct[k]++; }
                if (ds != 0) { dbad[k]++; printf("  DIRECT n = %lld: %s\n", n, ds == 2 ? "HALTS" : ds == 3 ? "bad" : "too long"); fflush(stdout); }
                else { if (dc > dmax_lvl[k]) { dmax_lvl[k] = dc; dmax_n[k] = n; } if (dj > Jmax) { Jmax = dj; Jmax_n = n; } }
                if (k < K) for (int delta = 1; delta >= 0; delta--) {
                    ll r2 = nd.rho + delta * (1LL << k);
                    if (nparts > 1 && k + 1 == splitlvl && (int)((((unsigned long long)r2 * 2654435761ULL) >> 16) % nparts) != part) continue;
                    if (top + 1 >= cap) { cap *= 2; stk = realloc(stk, sizeof(Node) * cap); }
                    Node *c = &stk[top++]; c->k = k + 1; c->rho = r2; stcpy(&c->st, &start); refine(&c->st, delta); c->nthr = nthr0; c->rounds = rounds - 1;
                }
                break;
            }
            if (S.halted || S.bad) { cbad[nd.k]++; printf("  class n = %lld (mod 2^%d): %s (%d)\n", nd.rho, nd.k, S.halted ? "HALTS" : "contact/bad", S.bad); fflush(stdout); break; }
            if (at_clean()) {
                int k = nd.k; if (!own) break; settled[k]++;
                ll jump = (S.W.b - (2 * nd.rho + 6)) / 2;
                i128 t = NTHR - nd.rho; ll jmin = 0; if (t > 0) { i128 q = t >> k; if ((q << k) < t) q++; jmin = (ll)q; }
                if (jmin > jminmax[k]) { jminmax[k] = jmin; jmin_rho[k] = nd.rho; }
                if (jmin >= 2) { fprintf(stderr, "%d %lld %lld %lld %d\n", k, nd.rho, jmin, jump, S.maxchain); }
                int ch = S.maxchain > 63 ? 63 : S.maxchain; chainh[ch]++; if (ch > maxchain_lvl[k]) maxchain_lvl[k] = ch;
                if (jump > Jmax) { Jmax = jump; Jmax_n = nd.rho + (1LL << k); }
                { int bi = (int)floor((S.maxh + 8.0) * 8.0); if (bi < 0) bi = 0; if (bi > 639) bi = 639; TAILB[bi] += ldexpl(1.0L, -k);
                  if (S.maxh >= 12.0) fprintf(stderr, "D %d %lld %.4f %d %lld\n", k, nd.rho, S.maxh, S.maxchain, jump); }
                if (ch >= 13) { printf("  chain %d: n = %lld (mod 2^%d), jump %lld\n", ch, nd.rho, k, jump); fflush(stdout); }
                break;
            }
            if (rounds >= 20000) { cbad[nd.k]++; printf("  class n = %lld (mod 2^%d): too long\n", nd.rho, nd.k); break; }
        }
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
    { long double open_meas = ldexpl((long double)openc[K], -K);
      printf("open measure after level %d: %.6Le\n", K, open_meas);
      for (int b = 0; b < 640; b++) if (TAILB[b] > 0) printf("hbin %.3f %.10Le\n", b / 8.0 - 8.0, TAILB[b]); }
    printf("totals: settled classes %lld, direct runs %lld, problems %lld, largest j_min %lld, largest jump %lld (n = %lld), longest chain %d\n", ts, td, tb, jm, Jmax, Jmax_n, oc);
    return 0;
}
