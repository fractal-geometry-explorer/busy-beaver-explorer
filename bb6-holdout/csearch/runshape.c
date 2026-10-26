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
typedef long long ll; typedef __int128 i128; typedef unsigned long long ull_t;
typedef struct { i128 a, b; } Q;
static const char *i128s(i128 v) { static char buf[4][64]; static int k = 0; char *b = buf[k++ & 3], t[64]; int n = 0, neg = v < 0; if (neg) v = -v;
    do { t[n++] = '0' + (int)(v % 10); v /= 10; } while (v); int j = 0; if (neg) b[j++] = '-'; while (n) b[j++] = t[--n]; b[j] = 0; return b; }

#define MAXM 256
static int CK; static ll CRHO; static i128 NTHR;
static inline void need_j(ll jr) { i128 t = (i128)CRHO + ((i128)jr << CK); if (t > NTHR) NTHR = t; }
static inline int qcmp(Q x, Q y) {
    if (x.a != y.a) return x.a < y.a ? -1 : 1;
    if (x.b != y.b) return x.b < y.b ? -1 : 1;
    return 0;
}
static inline Q qadd(Q x, i128 c) { x.b += c; return x; }
typedef struct {
    int nm; Q W; int halted, bad, need;
    int haslast, lastr, chain, maxchain; Q lastd; int ff; double maxh; int n5w; int n4w;
    int head, tail, alive, alld;
    char T[MAXM]; char A[MAXM]; unsigned char D[MAXM]; short nx[MAXM], pv[MAXM]; Q P[MAXM];
} St;
static inline void stcpy(St *d, const St *s) {
    memcpy(d, s, offsetof(St, T)); int n = s->nm;
    memcpy(d->T, s->T, n); memcpy(d->A, s->A, n); memcpy(d->D, s->D, n); memcpy(d->nx, s->nx, n * sizeof(short)); memcpy(d->pv, s->pv, n * sizeof(short)); memcpy(d->P, s->P, n * sizeof(Q));
}
static St S;
/* ---- probes ---- */
static ll minsep[3][4][4], minsep_n[3][4][4]; static ll PROBE_N, PJ;
static int LOGON = 0, NLOG = 0; static struct { short a, x, y; ll v, n; } ULOG[4096];
static const int TI[128] = { ['G'] = 0, ['M'] = 1, ['W'] = 2, ['B'] = 3 };
static const int LENT[4] = {3, 2, 2, 3};
/* which marks' pairs changed since the last probe of each phase: S.D[i] (bit p for phase p), S.alld (every pair),
   kept in the state so that a refined child, or a direct run, starts from the parent's probes at the start of the
   split round (those values are at the parent's smallest member, a smaller n, so they bound the child's from below
   and skipping them changes no minimum) */
static short DL[3][MAXM]; static int NDL[3];
static inline void dirty(int i) { if (i < 0) return; unsigned char d = S.D[i];
    if (!(d & 1)) DL[0][NDL[0]++] = i; if (!(d & 2)) DL[1][NDL[1]++] = i; if (!(d & 4)) DL[2][NDL[2]++] = i; S.D[i] = 7; }
static void rebuild_dl(void) { NDL[0] = NDL[1] = NDL[2] = 0;
    for (int i = 0; i < S.nm; i++) { unsigned char d = S.D[i]; if (d & 1) DL[0][NDL[0]++] = i; if (d & 2) DL[1][NDL[1]++] = i; if (d & 4) DL[2][NDL[2]++] = i; } }
static inline void evpair(int phase, int u, int v) {
    ll sp = (S.P[v].a * PJ + S.P[v].b) - (S.P[u].a * PJ + S.P[u].b + LENT[TI[(int)S.T[u]]]);
    int x = TI[(int)S.T[u]], y = TI[(int)S.T[v]];
    if (sp < minsep[phase][x][y]) {
        if (LOGON) { if (NLOG >= 4096) { fprintf(stderr, "undo log full\n"); exit(5); }
            ULOG[NLOG].a = phase; ULOG[NLOG].x = x; ULOG[NLOG].y = y; ULOG[NLOG].v = minsep[phase][x][y]; ULOG[NLOG].n = minsep_n[phase][x][y]; NLOG++; }
        minsep[phase][x][y] = sp; minsep_n[phase][x][y] = PROBE_N;
    }
}
static void probe(int phase) { return;
    int bit = 1 << phase; short *L = DL[phase]; int nl = NDL[phase];
    if (S.alld & bit) {
        for (int i = S.head; i >= 0 && S.nx[i] >= 0; i = S.nx[i]) evpair(phase, i, S.nx[i]);
        S.alld &= ~bit;
    } else {
        for (int t = 0; t < nl; t++) { int i = L[t];
            if (!S.A[i]) continue;
            if (S.pv[i] >= 0) evpair(phase, S.pv[i], i);
            if (S.nx[i] >= 0) evpair(phase, i, S.nx[i]); }
    }
    for (int t = 0; t < nl; t++) S.D[L[t]] &= ~bit;
    NDL[phase] = 0;
}
static void undo_log(void) { while (NLOG > 0) { NLOG--; minsep[ULOG[NLOG].a][ULOG[NLOG].x][ULOG[NLOG].y] = ULOG[NLOG].v; minsep_n[ULOG[NLOG].a][ULOG[NLOG].x][ULOG[NLOG].y] = ULOG[NLOG].n; } }
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
/* ---- run-shape statistics (point mode) ---- */
static int CAND, CANDAGE, CANDMET; static long CANDCH; static int CANDMP; static i128 CR, CW, CL1; static char CSH1[16];
static char RING[32][16]; static int RN;
static long CHID, LASTEMIT; static double CHH0; static int PEND; static i128 PR, PW, PL1; static i128 CURN;
static long HS[200], HM[16], HH0[200], NEMIT, NCH; static double MAXS = -1, MAXH0 = -1, MAXL = -99; static i128 MAXSN, MAXH0N, MAXLN; static int MAXSM;
static long HJ[16]; static long HSG[200]; static double MAXSG = -99, MAXSGs, MAXSGl; static int MAXSGm; static i128 MAXSGN;   /* M_pre by s bin, for s >= 5 */
static void rs_meeting(i128 d) {
    double h = log2((double)S.W.b) - log2((double)(d > 0 ? d : 1));
    if (S.chain == 1 && getenv("RH0") && h >= atof(getenv("RH0"))) { fprintf(stderr, "H0 %.3f n %s %s :", h, i128s(CURN >> 64), i128s(CURN & (((i128)1 << 64) - 1))); for (int k = (RN > 24 ? RN - 24 : 0); k < RN; k++) fprintf(stderr, " %s", RING[k & 31]); fprintf(stderr, "\n"); }
    if (S.chain == 1) { CHID++; CHH0 = h; NCH++; int b = (int)(h * 4); if (b < 0) b = 0; if (b > 199) b = 199; HH0[b]++; if (h > MAXH0) { MAXH0 = h; MAXH0N = CURN; } }
    if (CAND && !CANDMET) { CANDMET = 1; CANDCH = CHID; CANDMP = S.chain - 1; }
}
static void rs_emit(void) {
        if (CANDCH != LASTEMIT) { LASTEMIT = CANDCH; NEMIT++;
            double sv = log2((double)PW) - log2((double)PR); int mpre = CANDMP;
            int b = (int)(sv * 4); if (b < 0) b = 0; if (b > 199) b = 199; HS[b]++; HM[mpre < 15 ? mpre : 15]++;
            if (sv > MAXS) { MAXS = sv; MAXSN = CURN; MAXSM = mpre; }
            double lv = log2((double)(PL1 < 0 ? -PL1 : PL1)) - log2((double)PW); if (lv > MAXL) { MAXL = lv; MAXLN = CURN; }
            double sg = 3 * sv + 2 * lv; int bs = (int)(sg * 2); if (bs < 0) bs = 0; if (bs > 199) bs = 199; HSG[bs]++;
            if (getenv("RSG") && sg >= atof(getenv("RSG"))) fprintf(stderr, "SG %s %s sigma %.3f s %.3f start %.3f mpre %d lam %.3f\n", i128s(CURN >> 64), i128s(CURN & (((i128)1 << 64) - 1)), sg, sv, CHH0, mpre, lv);
            if (sg > MAXSG) { MAXSG = sg; MAXSGN = CURN; MAXSGs = sv; MAXSGl = lv; MAXSGm = mpre; }
        }
}
/* ---- census of repeating round patterns (env PAT) ---- */
#define PRING 64
static char PSH[PRING][24]; static int PN; static i128 PSNP[PRING][40]; static char PST[PRING][40]; static int PCNT[PRING]; static i128 PW_[PRING];
static int PRUN[17];
#define NPAT 4000
static char PKEY[NPAT][400]; static long PCOUNT[NPAT]; static int PMAXREP[NPAT]; static int NP_;
static void pat_round(int r) {
    if (r == 1) { PN = 0; for (int k = 0; k < 17; k++) PRUN[k] = 0; }
    int t = PN % PRING; int q = 0; int c = 0;
    for (int i = S.head; i >= 0 && q < 23; i = S.nx[i]) { PSH[t][q++] = S.T[i]; if (c < 40) { PST[t][c] = S.T[i]; PSNP[t][c] = S.P[i].b; c++; } }
    PSH[t][q] = 0; PCNT[t] = c; PW_[t] = S.W.b; PN++;
    for (int P = 1; P <= 16; P++) {
        if (PN <= P) { PRUN[P] = 0; continue; }
        if (!strcmp(PSH[(PN - 1) % PRING], PSH[(PN - 1 - P) % PRING])) PRUN[P]++; else PRUN[P] = 0;
        if (PRUN[P] == P) {           /* two full periods just completed */
            int minimal = 1; for (int d = 1; d < P; d++) if (P % d == 0 && PRUN[d] >= P) { minimal = 0; break; }
            if (!minimal) continue;
            /* canonical key: smallest rotation of the P shapes */
            char seq[16][24]; for (int k = 0; k < P; k++) strcpy(seq[k], PSH[(PN - P + k) % PRING]);
            char best[400] = "", cand[400];
            for (int rot = 0; rot < P; rot++) { cand[0] = 0; for (int k = 0; k < P; k++) { strcat(cand, seq[(rot + k) % P]); strcat(cand, k < P - 1 ? "," : ""); } if (!best[0] || strcmp(cand, best) < 0) strcpy(best, cand); }
            int id = -1; for (int k = 0; k < NP_; k++) if (!strcmp(PKEY[k], best)) { id = k; break; }
            if (id < 0 && NP_ < NPAT) { id = NP_++; strcpy(PKEY[id], best); PCOUNT[id] = 0; PMAXREP[id] = 0;
                /* an instance: the state at the start of the last period, and the period's shapes from there */
                int s0 = (PN - 1 - P) % PRING;
                fprintf(stderr, "PATNEW %d %s | start(%s)", P, best, PSH[s0]);
                for (int k = 0; k < PCNT[s0]; k++) fprintf(stderr, " %c%s", PST[s0][k], i128s(PSNP[s0][k]));
                fprintf(stderr, " width=%s | seq", i128s(PW_[s0])); for (int k = 0; k < P; k++) fprintf(stderr, " %s", seq[k]); fprintf(stderr, "\n");
            }
            if (id >= 0) PCOUNT[id]++;
        }
        if (PRUN[P] >= P) { int reps = PRUN[P] / P + 1; char seq2[400] = ""; (void)seq2;
            /* update max repetitions for the pattern found at this period (look it up by recomputing the key) */
            char seq[16][24]; for (int k = 0; k < P; k++) strcpy(seq[k], PSH[(PN - P + k) % PRING]);
            char best[400] = "", cand[400];
            for (int rot = 0; rot < P; rot++) { cand[0] = 0; for (int k = 0; k < P; k++) { strcat(cand, seq[(rot + k) % P]); strcat(cand, k < P - 1 ? "," : ""); } if (!best[0] || strcmp(cand, best) < 0) strcpy(best, cand); }
            for (int k = 0; k < NP_; k++) if (!strcmp(PKEY[k], best)) { if (reps > PMAXREP[k]) PMAXREP[k] = reps; break; }
        }
    }
}
static void pat_report(void) {
    if (!getenv("PAT")) return;
    printf("repeating patterns: %d kinds\n", NP_);
    for (int k = 0; k < NP_; k++) printf("  %8ld times, up to %d periods: %s\n", PCOUNT[k], PMAXREP[k], PKEY[k]);
}
static void rs_round(int r) {
    if (getenv("PAT")) pat_round(r);
    char sh[16]; int q = 0; for (int i = S.head; i >= 0 && q < 15; i = S.nx[i]) sh[q++] = S.T[i]; sh[q] = 0;
    if (r == 1) RN = 0; strcpy(RING[RN++ & 31], sh);
    if (r == 1) CAND = 0;
    if (CAND) { CANDAGE++;
        if (CANDAGE == 1) { if (strcmp(sh, "GBW")) CAND = 0; }
        else if (CANDAGE == 2) { if (!strcmp(sh, "GMB") && CANDMET) { PR = CR; PW = CW; PL1 = CL1; rs_emit(); } CAND = 0; } }
    if (!strcmp(sh, "GWWW")) {
        int i1 = S.nx[S.head], i2 = S.nx[i1], i3 = S.nx[i2];
        CR = S.W.b - S.P[i3].b - 1; CW = S.W.b; CL1 = 147 * S.P[i2].b + 280 * S.W.b - 392 * S.P[i3].b - 578; CAND = 1; CANDAGE = 0; CANDMET = 0; }
}
static void end_meeting(Q d, int r4) {
    if (!S.haslast) S.chain = 1;
    else { Q p = S.lastr == 2 ? (Q){ S.lastd.a / 2, (S.lastd.b - 2) / 2 } : (Q){ S.lastd.a / 2, S.lastd.b / 2 + 4 };
        if (qcmp(d, p) == 0) S.chain++; else S.chain = 1; }
    if (S.chain > S.maxchain) S.maxchain = S.chain;
    S.haslast = 1; S.lastd = d; S.lastr = r4;
    if (S.W.a == 0) rs_meeting(d.b);
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
            if (d.a < 0 || (d.a == 0 && d.b < 0) || (r4 & 1)) { S.bad = 3; return; }
            if (m == S.tail && getenv("TRACE") && S.W.a == 0) printf("  end meeting: d = %s (%s), %.3f halvings below the width, chain %d\n", i128s(d.b), r4 == 0 ? "swap" : "merge", log2((double)S.W.b) - log2((double)(d.b > 0 ? d.b : 1)), S.chain + 0);
            if (m == S.tail) { end_meeting(d, r4); double hv = d.a > 0 ? log2((double)S.W.a) - log2((double)d.a) : (S.W.a == 0 && d.b > 0 ? log2((double)S.W.b) - log2((double)d.b) : 99.0); if (hv > S.maxh) S.maxh = hv; }
            Q h = { d.a / 2, d.b / 2 };
            if (r4 == 0) { S.P[m] = (Q){ g.a + h.a, g.b + h.b - 1 }; S.P[gap] = (Q){ g.a + h.a, g.b + h.b + 1 }; fix(gap); fix(m); }
            else { killm(gap); S.T[m] = 'W'; S.P[m] = (Q){ g.a + h.a, g.b + h.b + 3 }; fix(m); gap = packet_back_from(m); }
        } else if (S.T[m] == 'W') { int s = S.nx[m]; killm(gap); killm(m); gap = shift_from_succ(s); }
        else if (S.T[m] == 'B') { S.T[m] = 'W'; S.P[m].b -= 1; fix(m); gap = shift_from_succ(S.nx[m]); }
        else { S.bad = 4; return; }
    }
    if (S.halted || S.bad || S.need) return;
    i128 extra = 2; int h0 = S.head;
    if (h0 >= 0 && S.T[h0] == 'M' && qcmp(S.P[h0], (Q){0, 0}) == 0) { S.T[h0] = 'W'; S.P[h0].b = 1; extra = 4; fix(h0); }
    for (int i = S.head; i >= 0; i = S.nx[i]) S.P[i].b += extra;
    S.W.b += extra; addm_after('G', (Q){0, 1}, -1);
}

static void init_line(Q m, Q W) {
    memset(&S, 0, offsetof(St, T)); S.head = S.tail = -1; S.W = W; S.alld = 7; S.maxh = -99;
    addm_after('G', (Q){0, 1}, -1); addm_after('M', m, S.head); addm_after('M', qadd(S.W, -2), S.tail);
}
static int seg_end(void) {
    if (S.tail < 0 || S.T[S.tail] != 'M' || qcmp(S.P[S.tail], qadd(S.W, -2)) != 0) return 0;
    if (S.alive == 2) return 1;
    if (S.alive == 3 && S.T[S.head] == 'G' && S.P[S.head].a == 0 && S.P[S.head].b == 1 && S.T[S.nx[S.head]] == 'M') return 2;
    return 0;
}
static void refine(St *s, int delta) {
    for (int i = 0; i < s->nm; i++) { Q p = s->P[i]; s->P[i] = (Q){ 2 * p.a, p.a * delta + p.b }; }
    Q w = s->W; s->W = (Q){ 2 * w.a, w.a * delta + w.b };
}
typedef struct { St st; int k; i128 x0; int rounds; } Node;   /* the class t = x0 + 2^k y */

/* ---- the line-up of a pass start: most passes any member can make, from the two countdowns ---- */
static int v2i(i128 x) { if (x == 0) return 999; int k = 0; if (x < 0) x = -x; while (!(x & 1)) { x >>= 1; k++; } return k; }
static i128 inv2(i128 a, int k) { /* inverse of odd a mod 2^k, k <= 120 */ i128 x = 1; for (int i = 0; i < 7; i++) x = x * (2 - a * x); i128 m = ((i128)1 << k) - 1; return x & m; }
/* solutions y of alpha*y + beta == 0 mod 2^e: returns 0 none, 1 all y, 2 y == *y0 mod 2^*md */
static int cong(i128 alpha, i128 beta, int e, i128 *y0, int *md) {
    int a = v2i(alpha);
    if (a >= e) return v2i(beta) >= e ? 1 : 0;
    if (v2i(beta) < a) return 0;
    int k = e - a; i128 m = ((i128)1 << k) - 1;
    i128 al = alpha >> a, be = beta >> a;            /* exact shifts (divisible) */
    if (alpha < 0) { al = -((-alpha) >> a); } if (beta < 0) { be = -((-beta) >> a); }
    *y0 = ((-be) & m) * inv2(al & m, k) & m; *md = k; return 2;
}
static int maxpasses(i128 aR, i128 bR, i128 aL, i128 bL) {
    int m = 0;
    for (; m < 18; m++) {
        int e1 = 4 * (m + 1) + 1, e2 = 6 * (m + 1) + 1; i128 y1 = 0, y2 = 0; int k1 = 0, k2 = 0;
        int c1 = cong(aR, bR, e1, &y1, &k1), c2 = cong(aL, bL, e2, &y2, &k2);
        if (!c1 || !c2) break;
        if (c1 == 2 && c2 == 2) { int k = k1 < k2 ? k1 : k2; i128 mk = ((i128)1 << k) - 1; if (((y1 - y2) & mk) != 0) break; }
    }
    return m;
}
/* loop meetings: each meeting uses one trailing zero of R and, on average, 1.5 of L */
static int maxmeet(i128 aR, i128 bR, i128 aL, i128 bL) {
    int j = 0;
    for (; j < 70; j++) {
        int e1 = (j + 1) + 1, e2 = (3 * (j + 1)) / 2 + 1; i128 y1 = 0, y2 = 0; int k1 = 0, k2 = 0;
        int c1 = cong(aR, bR, e1, &y1, &k1), c2 = cong(aL, bL, e2, &y2, &k2);
        if (!c1 || !c2) break;
        if (c1 == 2 && c2 == 2) { int k = k1 < k2 ? k1 : k2; i128 mk = ((i128)1 << k) - 1; if (((y1 - y2) & mk) != 0) break; }
    }
    return j;
}
static double PRED; static int PREDM; static double PREDH;
static Node *STK; static int CAP; static int MAX5W; static long double M5W[8]; static int MAX4W; static long double M4W[16]; static i128 X5W; static int K5W; static long double TT[32]; static int MINK[32]; static i128 MINX0[32]; static i128 MINT[32]; static int MINTK[32];
static void run_line(int cut, ll am, ll m0, ll aE, ll E0, double *reach, i128 *bx0, int *bk, long double *lostp, long double *t12, long double *t14) {
    int top = 0; static St start;
    init_line((Q){ am, m0 }, (Q){ aE, E0 });
    STK[top].st = S; STK[top].k = 0; STK[top].x0 = 0; STK[top].rounds = 0; top++;
    PRED = -99; PREDM = 0; PREDH = 0;
    MAX5W = 0; for (int x = 0; x < 8; x++) M5W[x] = 0; MAX4W = 0; for (int x = 0; x < 16; x++) M4W[x] = 0;
    *reach = -99; *bx0 = 0; *bk = 0; long double lost = 0, a12 = 0, a14 = 0; for (int x = 0; x < 32; x++) TT[x] = 0; for (int x = 0; x < 32; x++) { MINK[x] = 999; MINT[x] = -1; }
    while (top > 0) {
        top--; Node nd; nd.k = STK[top].k; nd.x0 = STK[top].x0; nd.rounds = STK[top].rounds; stcpy(&S, &STK[top].st);
        for (;;) {
            stcpy(&start, &S);
            do_round(); nd.rounds++;
            if (S.need) {
                if (nd.k >= cut) { lost += ldexpl(1.0L, -nd.k); break; }
                for (int delta = 1; delta >= 0; delta--) {
                    if (top + 1 >= CAP) { CAP *= 2; STK = realloc(STK, sizeof(Node) * CAP); }
                    Node *c = &STK[top++]; c->k = nd.k + 1; c->x0 = nd.x0 + ((i128)delta << nd.k); stcpy(&c->st, &start); refine(&c->st, delta); c->rounds = nd.rounds - 1;
                }
                break;
            }
            { int c = 0, ok = 1; int i = S.head; if (i < 0 || S.T[i] != 'G') ok = 0; else { for (i = S.nx[i]; i >= 0; i = S.nx[i]) { if (S.T[i] != 'W') { ok = 0; break; } c++; } }
              if (ok && c == 4) S.n5w++; if (ok && c == 3) S.n4w++;
              if (ok && c == 3 && getenv("KAPPA")) { int i1 = S.nx[S.head], i2 = S.nx[i1], i3 = S.nx[i2];
                  Q b = S.P[i2], cc = S.P[i3], E = S.W;
                  i128 aR = E.a - cc.a, bR = E.b - cc.b - 1, aL = 147 * b.a + 280 * E.a - 392 * cc.a, bL = 147 * b.b + 280 * E.b - 392 * cc.b - 578;
                  int m = maxmeet(aR, bR, aL, bL); double h = (S.maxh > 0 ? S.maxh : 0) + m + 3;
                  if (h > PRED) { PRED = h; PREDM = m; PREDH = S.maxh; } } }
            if (S.halted || S.bad) { printf("HALTBAD %lld %lld %lld %lld k %d bad %d\n", am, m0, aE, E0, nd.k, S.bad); break; }
            if (S.nm > 0 && seg_end() && nd.rounds > 0) {
                if (S.n4w > MAX4W) MAX4W = S.n4w; for (int x = 0; x < 16 && x <= S.n4w; x++) M4W[x] += ldexpl(1.0L, -nd.k);
                if (S.n5w > MAX5W) { MAX5W = S.n5w; X5W = nd.x0; K5W = nd.k; } for (int x = 0; x < 8 && x <= S.n5w; x++) M5W[x] += ldexpl(1.0L, -nd.k);
                if (S.maxh > *reach) { *reach = S.maxh; *bx0 = nd.x0; *bk = nd.k; }
                for (int x = 10; x < 32 && x <= S.maxh; x++) if (MINT[x] < 0 || nd.x0 < MINT[x]) { MINT[x] = nd.x0; MINTK[x] = nd.k; }
                for (int x = 10; x < 32 && x <= S.maxh; x++) if (nd.k < MINK[x] || (nd.k == MINK[x] && nd.x0 < MINX0[x])) { MINK[x] = nd.k; MINX0[x] = nd.x0; }
                for (int x = 0; x < 32 && x <= S.maxh; x++) TT[x] += ldexpl(1.0L, -nd.k);
                if (S.maxh >= 12) a12 += ldexpl(1.0L, -nd.k);
                if (S.maxh >= 14) a14 += ldexpl(1.0L, -nd.k);
                break;
            }
            if (nd.rounds >= 3000) { lost += ldexpl(1.0L, -nd.k); break; }
        }
    }
    *lostp = lost; *t12 = a12; *t14 = a14;
}
/* direct integer run of the whole cycle of clean tape n (positions are constants), closest end meeting in halvings */
static i128 SEGM, SEGE, BESTM, BESTE; static double BESTH;
static void point_cycle(i128 n) {
    SEGM = 0; SEGE = 0; BESTM = 0; BESTE = 0; BESTH = -99;
    init_line((Q){0, 0}, (Q){0, 0});
    memset(&S, 0, offsetof(St, T)); S.head = S.tail = -1; S.W = (Q){0, 2 * n + 6}; S.alld = 7;
    addm_after('G', (Q){0, 1}, -1); addm_after('M', qadd(S.W, -2), S.tail);
    double best = -99; int segs = 0, rounds = 0;
    for (int r = 1; r <= 100000; r++) {
        /* closest end meeting this round: track via S.maxh with actual values */
        do_round(); rounds = r;
        rs_round(r);
        if (0) { char sh[16]; int q = 0; static char h1[16], h2[16];
          if (!strcmp(sh, "GWWW") && !strcmp(h1, "GBW") && !strcmp(h2, "GWWW")) {
              int i1 = S.nx[S.head], i2 = S.nx[i1], i3 = S.nx[i2];
              PR = S.W.b - S.P[i3].b - 1; PW = S.W.b; PL1 = 147 * S.P[i2].b + 280 * S.W.b - 392 * S.P[i3].b - 578; PEND = 1; }
          strcpy(h2, h1); strcpy(h1, sh); }
        if (getenv("TRACE")) { printf("round %d:", r); for (int i = S.head; i >= 0; i = S.nx[i]) printf("%c", S.T[i]); printf("\n"); }
        if (getenv("TRACEP") && r >= atoi(getenv("TRACEP"))) { printf("   W-p:"); for (int i = S.head; i >= 0; i = S.nx[i]) printf(" %c%s", S.T[i], i128s(S.W.b - S.P[i].b)); printf("  W %s\n", i128s(S.W.b)); }
        if (getenv("PASSES")) { int i = S.head, c = 0, ok = (i >= 0 && S.T[i] == 'G'); i128 w[8];
            if (ok) for (i = S.nx[i]; i >= 0; i = S.nx[i]) { if (S.T[i] != 'W' || c >= 8) { ok = 0; break; } w[c++] = S.P[i].b; }
            if (ok && c == 3) printf("PASS round %d a %s b %s c %s E %s\n", r, i128s(w[0]), i128s(w[1]), i128s(w[2]), i128s(S.W.b)); }
        if (S.halted || S.bad || S.need) { printf("n run stopped: halted %d bad %d need %d\n", S.halted, S.bad, S.need); return; }
        if (S.alive == 2 && S.T[S.tail] == 'M' && qcmp(S.P[S.tail], qadd(S.W, -2)) == 0) break;
        if (S.maxh > BESTH) { BESTH = S.maxh; BESTM = SEGM; BESTE = SEGE; }
        if (seg_end() == 2) { segs++; SEGM = S.P[S.nx[S.head]].b; SEGE = S.W.b; }
    }
    best = S.maxh;
    if (getenv("SEGOUT")) printf("SEG %s %s\n", i128s(BESTM), i128s(BESTE));
    printf("n done: rounds %d, segments %d, closest end meeting %.4f halvings below the width, longest chain %d, next clean tape n' - n = %lld\n", rounds, segs, best, S.maxchain, (ll)((S.W.b - 2 * n - 6) / 2));
}
int main(int argc, char **argv) {
    if (argv[1][0] == 'F') {   /* F : lines "W t1 p1 t2 p2 ..." (t in G M W B), run until a segment ends; loop-entry stats */
        static char line[8192]; long cnt = 0, nseg = 0, nhb = 0;
        while (fgets(line, sizeof line, stdin)) {
            char *tok = strtok(line, " \t\n"); if (!tok) continue;
            i128 W = 0; for (char *p = tok; *p; p++) W = W * 10 + (*p - '0');
            memset(&S, 0, offsetof(St, T)); S.head = S.tail = -1; S.W = (Q){0, W}; S.alld = 7; S.maxh = -99;
            int ok = 1, after = -1;
            while ((tok = strtok(NULL, " \t\n"))) { char t = tok[0]; char *v = strtok(NULL, " \t\n"); if (!v) { ok = 0; break; }
                i128 p = 0; for (char *q = v; *q; q++) p = p * 10 + (*q - '0');
                after = addm_after(t, (Q){0, p}, after < 0 ? -1 : S.tail); if (after < 0) { ok = 0; break; } after = S.tail; }
            if (!ok) continue;
            cnt++; CURN = W; PEND = 0; LASTEMIT = -1; CHID = 0;
            for (int r = 1; r <= 3000; r++) { do_round(); rs_round(r);
                if (S.halted || S.bad || S.need) { nhb++; break; }
                if (seg_end()) { nseg++; break; } }
        }
        printf("states %ld: segments ended %ld, halted/bad %ld; chains %ld loop entries %ld\n", cnt, nseg, nhb, NCH, NEMIT);
        printf("max s %.3f; max run-start halvings %.3f; max |L1|/W 2^%.2f\n", MAXS, MAXH0, MAXL);
        printf("max sigma %.3f with s %.3f, log2(|L1|/W) %.3f, M_pre %d\n", MAXSG, MAXSGs, MAXSGl, MAXSGm);
        long acc = 0; printf("sigma, cumulative from the top:"); for (int b = 199; b >= 0; b--) if (HSG[b]) { acc += HSG[b]; if (b % 2 == 0) printf(" >=%d:%ld", b / 2, acc); } printf("\n");
        return 0; }
    if (argv[1][0] == 'G') {   /* G : GMM states "m E" from stdin, one segment each, every loop entry printed */
        ll m, E;
        while (scanf("%lld %lld", &m, &E) == 2) {
            CURN = ((i128)m << 64) | E; PEND = 0; LASTEMIT = -1; CHID = 0;
            init_line((Q){0, m}, (Q){0, E}); double best = -99;
            for (int r = 1; r <= 100000; r++) { do_round(); rs_round(r);
                if (S.halted || S.bad || S.need) { printf("stopped\n"); break; }
                if (seg_end()) break; }
            printf("state (%lld, %lld): closest %.3f, entries %ld, max sigma so far %.3f\n", m, E, S.maxh, NEMIT, MAXSG);
        }
        return 0; }
    if (argv[1][0] == 'g') {   /* g bits count seed : random GMM states (m even, E odd, width about 2^bits), one segment each */
        int bits = atoi(argv[2]); long cnt = atol(argv[3]); unsigned long long sd = strtoull(argv[4], 0, 10); long nseg = 0, nhb = 0;
        for (long t = 0; t < cnt; t++) {
            sd = sd * 6364136223846793005ULL + 1442695040888963407ULL; unsigned long long x = sd ^ (sd >> 31);
            sd = sd * 6364136223846793005ULL + 1442695040888963407ULL; unsigned long long y = sd ^ (sd >> 29);
            ll E = ((ll)1 << (bits - 1)) | (ll)(x & (((ull_t)1 << (bits - 1)) - 1)); E |= 1;
            ll m = 4 + 2 * (ll)(y % (ull_t)((E - 7 - 4) / 2 + 1));
            CURN = ((i128)m << 64) | E; PEND = 0; LASTEMIT = -1; CHID = 0;
            init_line((Q){0, m}, (Q){0, E});
            for (int r = 1; r <= 100000; r++) { do_round(); rs_round(r);
                if (S.halted || S.bad || S.need) { nhb++; break; }
                if (seg_end()) { nseg++; break; } }
        }
        printf("GMM states %ld (bits %d): segments ended %ld, halted/bad %ld; chains %ld loop entries %ld\n", cnt, bits, nseg, nhb, NCH, NEMIT); pat_report();
        printf("max s %.3f at (m,E) = (%s, %s) (M_pre %d); max run-start halvings %.3f; max |L1|/W 2^%.2f\n", MAXS, i128s(MAXSN >> 64), i128s(MAXSN & (((i128)1 << 64) - 1)), MAXSM, MAXH0, MAXL);
        long acc = 0; printf("s, cumulative from the top:"); for (int b = 199; b >= 0; b--) if (HS[b]) { acc += HS[b]; if (b % 2 == 0) printf(" >=%.1f:%ld", b / 4.0, acc); } printf("\n");
        printf("M_pre:"); for (int mm = 0; mm < 16; mm++) printf(" %d:%ld", mm, HM[mm]); printf("\n");
        printf("max sigma = 3s + 2 log2(|L1|/W): %.3f at (%s, %s) with s %.3f, log2(|L1|/W) %.3f, M_pre %d\n", MAXSG, i128s(MAXSGN >> 64), i128s(MAXSGN & (((i128)1 << 64) - 1)), MAXSGs, MAXSGl, MAXSGm);
        acc = 0; printf("sigma, cumulative from the top:"); for (int b = 199; b >= 0; b--) if (HSG[b]) { acc += HSG[b]; if (b % 2 == 0) printf(" >=%d:%ld", b / 2, acc); } printf("\n");
        acc = 0; printf("run starts, cumulative from the top:"); for (int b = 199; b >= 0; b--) if (HH0[b]) { acc += HH0[b]; if (b % 2 == 0 && b >= 4) printf(" >=%.1f:%ld", b / 4.0, acc); } printf("\n");
        return 0; }
    if (argv[1][0] == 's') {   /* s start count step | s r bits count seed : run-shape statistics */
        i128 st = 0; long cnt; int rnd = argv[2][0] == 'r';
        int fromin = argv[2][0] == '-'; static char nbuf[64];
        if (fromin) cnt = 1L << 40;
        else if (!rnd) { for (char *p = argv[2]; *p; p++) st = st * 10 + (*p - '0'); cnt = atol(argv[3]); }
        else cnt = atol(argv[4]);
        ll step = (rnd || fromin) ? 0 : atoll(argv[4]); int bits = rnd ? atoi(argv[3]) : 0; unsigned long long sd = rnd ? strtoull(argv[5], 0, 10) : 0;
        for (long t = 0; t < cnt; t++) {
            i128 n;
            if (rnd) { i128 x = 0; for (int w = 0; w < 2; w++) { sd = sd * 6364136223846793005ULL + 1442695040888963407ULL; x = (x << 64) | (sd ^ (sd >> 29)); }
                       i128 msk = ((i128)1 << (bits - 1)) - 1; n = ((i128)1 << (bits - 1)) | (x & msk); }
            else if (fromin) { if (scanf("%63s", nbuf) != 1) { cnt = t; break; } n = 0; for (char *p = nbuf; *p; p++) n = n * 10 + (*p - '0'); }
            else n = st + (i128)step * t;
            CURN = n; PEND = 0; LASTEMIT = -1; CHID = 0;
            FILE *sv = stdout; stdout = fopen("/dev/null", "w"); point_cycle(n); fclose(stdout); stdout = sv;
        }
        printf("cycles %ld chains %ld loop entries %ld\n", cnt, NCH, NEMIT); pat_report();
        printf("max s %.3f at n = %s (M_pre %d); max run-start halvings %.3f at n = %s; max |L1|/W 2^%.2f at n = %s\n", MAXS, i128s(MAXSN), MAXSM, MAXH0, i128s(MAXH0N), MAXL, i128s(MAXLN));
        printf("s histogram (quarter halvings, cumulative from the top):\n"); long acc = 0;
        for (int b = 199; b >= 0; b--) if (HS[b]) { acc += HS[b]; printf("  s >= %.2f: %ld\n", b / 4.0, acc); }
        printf("M_pre:"); for (int m = 0; m < 16; m++) printf(" %d:%ld", m, HM[m]); printf("\n");
        printf("max sigma = 3s + 2 log2(|L1|/W): %.3f at n = %s with s %.3f, log2(|L1|/W) %.3f, M_pre %d\n", MAXSG, i128s(MAXSGN), MAXSGs, MAXSGl, MAXSGm);
        { long ac2 = 0; printf("sigma, cumulative from the top:"); for (int b = 199; b >= 0; b--) if (HSG[b]) { ac2 += HSG[b]; if (b % 2 == 0) printf(" >=%d:%ld", b / 2, ac2); } printf("\n"); }
        printf("run starts (all chains), halvings, cumulative from the top:\n"); acc = 0;
        for (int b = 199; b >= 0; b--) if (HH0[b]) { acc += HH0[b]; if (b >= 8) printf("  h0 >= %.2f: %ld\n", b / 4.0, acc); }
        return 0; }
    if (argv[1][0] == 'n') { char buf[64]; while (scanf("%63s", buf) == 1) { i128 n = 0; for (char *p = buf; *p; p++) n = n * 10 + (*p - '0'); point_cycle(n); } return 0; }
    int cut = atoi(argv[1]); CAP = 1 << 10; STK = malloc(sizeof(Node) * CAP);
    int bits; ll am, m0, aE, E0, rd; char tag[8];
    while (scanf("%7s %d %lld %lld %lld %lld %lld", tag, &bits, &am, &m0, &aE, &E0, &rd) == 7) {
        double reach; i128 bx0; int bk; long double lost, t12, t14;
        run_line(cut, am, m0, aE, E0, &reach, &bx0, &bk, &lost, &t12, &t14);
        printf("R %d %lld %lld %lld %lld reach %.4f best_x0 %lld best_bits %d undecided %.3Le t12 %.3Le t14 %.3Le", bits, am, m0, aE, E0, reach, (ll)bx0, bk, lost, t12, t14);
        if (getenv("KAPPA")) printf(" pred %.3f meetings %d at %.3f", PRED, PREDM, PREDH);
        if (getenv("W4")) { printf(" w4max %d w4share", MAX4W); for (int x = 1; x < 9; x++) printf(" %.3Le", M4W[x]); }
        if (getenv("W5")) printf(" w5max %d w5share %.3Le %.3Le %.3Le at %s/%d", MAX5W, M5W[1], M5W[3], M5W[5], i128s(X5W), K5W);
        if (getenv("TAILS")) { printf(" tails"); for (int x = 10; x < 32; x++) printf(" %.4Le", TT[x]); }
        if (getenv("MINT")) { printf(" mint"); for (int x = 10; x < 32 && MINT[x] >= 0; x++) printf(" %d:%d:%s", x, MINTK[x], i128s(MINT[x])); }
        if (getenv("MINK")) { printf(" mink"); for (int x = 10; x < 32 && MINK[x] < 999; x++) printf(" %d:%d:%lld", x, MINK[x], (ll)MINX0[x]); }
        printf("\n");
        fflush(stdout);
    }
    return 0;
}
