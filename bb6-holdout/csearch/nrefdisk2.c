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
static ll jreq;   /* smallest j for which every comparison made so far comes out as in the symbolic run */
static inline void need_j(ll v) { if (v > jreq) jreq = v; }
static inline int qcmp(Q x, Q y) {
    if (x.a != y.a) {
        ll d = y.a - x.a, D = y.b - x.b;           /* actual difference y - x = d*j + D; symbolic sign = sign(d) */
        ll t = d > 0 ? -D : D, ad = d > 0 ? d : -d;  /* need ad*j > t */
        if (t >= 0) need_j(t / ad + 1);
        return x.a < y.a ? -1 : 1;
    }
    if (x.b != y.b) return x.b < y.b ? -1 : 1; return 0;
}
static inline Q qadd(Q x, ll c) { x.b += c; return x; }
#define MAXM 256
static char T[MAXM]; static Q P[MAXM]; static int A[MAXM]; static int nm;
static Q W; static int halted, bad, need;
static Q endd[8192]; static int endr[8192]; static int nend;
static ll minsep[3][4][4]; static ll minsep_n[3][4][4], CURN;
static int ti(char t) { return t == 'G' ? 0 : t == 'M' ? 1 : t == 'W' ? 2 : 3; }
static const int LENT[4] = {3, 2, 2, 3};
static void probe(int phase) {   /* separations between neighbouring marks, evaluated at j = 1 (the smallest member) */
    int idx[MAXM], k = 0;
    for (int i = 0; i < nm; i++) if (A[i]) idx[k++] = i;
    for (int i = 1; i < k; i++) { int v = idx[i], j = i - 1;
        while (j >= 0 && (P[idx[j]].a > P[v].a || (P[idx[j]].a == P[v].a && P[idx[j]].b > P[v].b))) { idx[j + 1] = idx[j]; j--; } idx[j + 1] = v; }
    for (int i = 0; i + 1 < k; i++) {
        int a = idx[i], b = idx[i + 1];
        ll sp = (P[b].a + P[b].b) - (P[a].a + P[a].b + LENT[ti(T[a])]);
        int x = ti(T[a]), y = ti(T[b]);
        if (sp < minsep[phase][x][y]) { minsep[phase][x][y] = sp; minsep_n[phase][x][y] = CURN; }
    }
}
static int add(char t, Q p) { for (int i = 0; i < nm; i++) if (!A[i]) { T[i] = t; P[i] = p; A[i] = 1; return i; }
    if (nm >= MAXM) { bad = 9; return 0; } T[nm] = t; P[nm] = p; A[nm] = 1; return nm++; }
static int first_right(Q x) { int b = -1; for (int i = 0; i < nm; i++) if (A[i] && qcmp(P[i], x) > 0 && (b < 0 || qcmp(P[i], P[b]) < 0)) b = i; return b; }
static int last_mark(void) { int b = -1; for (int i = 0; i < nm; i++) if (A[i] && (b < 0 || qcmp(P[i], P[b]) > 0)) b = i; return b; }
static int packet_back(Q x) {
    probe(2);
    int b = -1; for (int i = 0; i < nm; i++) if (A[i] && qcmp(P[i], x) < 0 && T[i] != 'M' && (b < 0 || qcmp(P[i], P[b]) > 0)) b = i;
    if (b < 0) return -1;
    if (T[b] == 'B') { halted = 1; return -1; }
    if (T[b] == 'G') { P[b].b += 2; return b; }
    Q q = P[b]; T[b] = 'M'; P[b] = qadd(q, -1); return add('G', qadd(q, 1));
}
static int shift_from(Q x) {
    probe(1);
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
        probe(0);
        Q g = P[gap]; int m = first_right(g);
        if (m < 0) { A[gap] = 0; W.b += 3; add('M', qadd(W, -2)); gap = packet_back(qadd(W, -2)); continue; }
        if (T[m] == 'M') {
            Q d = { P[m].a - g.a, P[m].b - g.b - 3 };
            if (d.a % 4) { need = 1; return; }
            int r4 = (int)(((d.b % 4) + 4) % 4);
            if (d.a > 0 && d.b < 0) need_j((-d.b + d.a - 1) / d.a);   /* the integer distance must not be negative */
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
    for (int i = 0; i < nm; i++) if (A[i] && T[i] == 'M' && qcmp(P[i], (Q){0, 0}) == 0) { T[i] = 'W'; P[i].b = 1; extra = 4; }
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
    nm = 0; halted = bad = need = 0; nend = 0; jreq = 0;
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
static int cycle_int(ll n, ll *jump, int *rounds, int *chain) {
    nm = 0; halted = bad = need = 0; nend = 0; jreq = 0;
    W = (Q){ 0, 2 * n + 6 };
    add('G', (Q){0, 1}); add('M', qadd(W, -2));
    for (int r = 1; r <= 20000; r++) {
        do_round();
        if (need) return 1;
        if (halted) return 2;
        if (bad) return 3;
        int alive = 0, ok = 0; Q e = qadd(W, -2);
        for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M' && qcmp(P[i], e) == 0) ok = 1; }
        if (alive == 2 && ok) { *jump = (W.b - (2 * n + 6)) / 2; *rounds = r; *chain = chain_len(); return 0; }
    }
    return 4;
}
/* ---------------- disk-backed, resumable, 2-worker driver ----------------
   Usage: nrefdisk K_max dir.  dir/open_K.bin holds the residues still open at depth K (to be run with K digits).
   A level is finished when dir/open_{K+1}.ok exists; a restart resumes from the deepest finished level.          */
#include <unistd.h>
#include <sys/wait.h>
#include <sys/stat.h>
#include <signal.h>
#include <sys/prctl.h>
typedef struct {
    long long settled, open2, hist[64], jh[64], direct, dbad, bad;
    ll jminmax, jminmax_rho, Jmax, Jmax_n; int dmax; ll dmax_n; int newmax;
    ll ms[3][4][4], msn[3][4][4];
} Stats;
static const char *DIR;
static void pth(char *b, const char *fmt, int k, int w) { char t[256]; sprintf(t, fmt, k, w); sprintf(b, "%s/%s", DIR, t); }
static int exists(const char *p) { struct stat st; return stat(p, &st) == 0; }
static long long fsize(const char *p) { struct stat st; return stat(p, &st) == 0 ? st.st_size : -1; }
static void worker_chunk(int k, int w, int c, long long lo, long long hi) {
    char p[512]; pth(p, "open_%d.bin", k, 0);
    FILE *in = fopen(p, "rb"); fseeko(in, lo * 8, SEEK_SET);
    sprintf(p, "%s/nx_%d_%d_%d.bin", DIR, k, w, c); char tmp[600]; sprintf(tmp, "%s.tmp", p); FILE *out = fopen(tmp, "wb");
    Stats S; memset(&S, 0, sizeof S);
    for (int a = 0; a < 3; a++) for (int x = 0; x < 4; x++) for (int y = 0; y < 4; y++) minsep[a][x][y] = 1LL << 62;
    ll buf[4096];
    for (long long i = lo; i < hi; ) {
        int nb = (int)((hi - i) < 4096 ? (hi - i) : 4096); if ((int)fread(buf, 8, nb, in) != nb) { fprintf(stderr, "read error\n"); _exit(2); }
        for (int t = 0; t < nb; t++, i++) {
            ll rho = buf[t], jump; int rounds, chain;
            static ll save[3][4][4], saven[3][4][4]; memcpy(save, minsep, sizeof minsep); memcpy(saven, minsep_n, sizeof minsep_n);
            CURN = rho + (1LL << k);
            int s = cycle(k, rho, &jump, &rounds, &chain);
            if (s != 0) { memcpy(minsep, save, sizeof minsep); memcpy(minsep_n, saven, sizeof minsep_n); }
            if (s == 1) {
                ll n = rho + (1LL << k), dj; int dr, dc; CURN = n; int ds = cycle_int(n, &dj, &dr, &dc); S.direct++;
                if (ds != 0) { S.dbad++; printf("  DIRECT n = %lld: %s\n", n, ds == 2 ? "HALTS" : ds == 3 ? "bad" : "too long"); fflush(stdout); }
                else { if (dc > S.dmax) { S.dmax = dc; S.dmax_n = n; } if (dj > S.Jmax) { S.Jmax = dj; S.Jmax_n = n; } }
                ll c2[2] = { rho, rho + (1LL << k) }; fwrite(c2, 8, 2, out); S.open2++;
                continue;
            }
            if (s == 0) {
                S.settled++; int bkt = 0; ll x = jreq; while (x > 0) { bkt++; x >>= 1; } S.jh[bkt]++;
                if (jreq > S.jminmax) { S.jminmax = jreq; S.jminmax_rho = rho; }
                if (jreq >= 2) { fprintf(stderr, "%d %lld %lld %lld %d %d\n", k, rho, jreq, jump, rounds, chain); }
                if (chain > 63) chain = 63; S.hist[chain]++; if (chain > S.newmax) S.newmax = chain;
                if (jump > S.Jmax) { S.Jmax = jump; S.Jmax_n = rho + (1LL << k); }
                if (chain >= 13) { printf("  chain %d: n = %lld (mod 2^%d), jump %lld\n", chain, rho, k, jump); fflush(stdout); }
            } else { S.bad++; printf("  class n = %lld (mod 2^%d): %s\n", rho, k, s == 2 ? "HALTS" : s == 3 ? "contact/bad" : "too long"); fflush(stdout); }
        }
    }
    fclose(in); fclose(out); rename(tmp, p);
    memcpy(S.ms, minsep, sizeof minsep); memcpy(S.msn, minsep_n, sizeof minsep_n);
    sprintf(p, "%s/st_%d_%d_%d.bin", DIR, k, w, c); sprintf(tmp, "%s.tmp", p); FILE *f = fopen(tmp, "wb"); fwrite(&S, sizeof S, 1, f); fclose(f); rename(tmp, p);
}
#define CH 4000000LL
static void worker(int k, int w, long long lo, long long hi) {
    char p[512];
    for (int c = 0; lo + (long long)c * CH < hi; c++) {
        sprintf(p, "%s/st_%d_%d_%d.bin", DIR, k, w, c); if (exists(p)) continue;
        long long a = lo + (long long)c * CH, b = a + CH < hi ? a + CH : hi;
        worker_chunk(k, w, c, a, b);
    }
}
int main(int argc, char **argv) {
    int K = atoi(argv[1]); DIR = argv[2]; mkdir(DIR, 0755);
    char p[512], q[512];
    /* global state: cumulative minsep and maxima */
    Stats G; memset(&G, 0, sizeof G);
    for (int a = 0; a < 3; a++) for (int x = 0; x < 4; x++) for (int y = 0; y < 4; y++) G.ms[a][x][y] = 1LL << 62;
    sprintf(p, "%s/global.bin", DIR); { FILE *f = fopen(p, "rb"); if (f) { if (fread(&G, sizeof G, 1, f) != 1) {} fclose(f); } }
    int k = 0; for (int t = 63; t >= 1 && !k; t--) { pth(p, "open_%d.ok", t, 0); if (exists(p)) k = t; }
    if (!k) { k = 1; pth(p, "open_%d.bin", 1, 0); FILE *f = fopen(p, "wb"); ll a[2] = {0, 1}; fwrite(a, 8, 2, f); fclose(f); pth(p, "open_%d.ok", 1, 0); fclose(fopen(p, "w")); }
    else printf("[resuming at depth %d]\n", k);
    fflush(stdout);
    for (; k <= K; k++) {
        pth(p, "open_%d.bin", k, 0); long long nc = fsize(p) / 8; if (nc <= 0) break;
        pid_t kids[2];
        for (int w = 0; w < 2; w++) {
            long long lo = nc * w / 2, hi = nc * (w + 1) / 2;
            kids[w] = fork();
            if (kids[w] == 0) { prctl(PR_SET_PDEATHSIG, SIGKILL); worker(k, w, lo, hi); _exit(0); }
        }
        for (int w = 0; w < 2; w++) if (kids[w] > 0) waitpid(kids[w], NULL, 0);
        Stats L; memset(&L, 0, sizeof L);
        for (int w = 0; w < 2; w++) for (int c = 0; nc * w / 2 + (long long)c * CH < nc * (w + 1) / 2; c++) {
            sprintf(q, "%s/st_%d_%d_%d.bin", DIR, k, w, c); FILE *f = fopen(q, "rb"); Stats S; if (!f || fread(&S, sizeof S, 1, f) != 1) { fprintf(stderr, "missing worker result %s\n", q); return 1; } fclose(f);
            L.settled += S.settled; L.open2 += S.open2; L.direct += S.direct; L.dbad += S.dbad; L.bad += S.bad;
            for (int c = 0; c < 64; c++) { L.hist[c] += S.hist[c]; L.jh[c] += S.jh[c]; }
            if (S.jminmax > L.jminmax) { L.jminmax = S.jminmax; L.jminmax_rho = S.jminmax_rho; }
            if (S.Jmax > L.Jmax) { L.Jmax = S.Jmax; L.Jmax_n = S.Jmax_n; }
            if (S.dmax > L.dmax) { L.dmax = S.dmax; L.dmax_n = S.dmax_n; }
            if (S.newmax > L.newmax) L.newmax = S.newmax;
            for (int a = 0; a < 3; a++) for (int x = 0; x < 4; x++) for (int y = 0; y < 4; y++) if (S.ms[a][x][y] < G.ms[a][x][y]) { G.ms[a][x][y] = S.ms[a][x][y]; G.msn[a][x][y] = S.msn[a][x][y]; }
        }
        /* next level file = concatenation of the workers' outputs */
        pth(p, "open_%d.bin", k + 1, 0); char tmp[600]; sprintf(tmp, "%s.tmp", p); FILE *o = fopen(tmp, "wb");
        for (int w = 0; w < 2; w++) for (int c = 0; nc * w / 2 + (long long)c * CH < nc * (w + 1) / 2; c++) { sprintf(q, "%s/nx_%d_%d_%d.bin", DIR, k, w, c); FILE *f = fopen(q, "rb"); static ll b[1 << 16]; size_t r; while ((r = fread(b, 8, 1 << 16, f)) > 0) fwrite(b, 8, r, o); fclose(f); }
        fclose(o); rename(tmp, p);
        if (L.Jmax > G.Jmax) { G.Jmax = L.Jmax; G.Jmax_n = L.Jmax_n; }
        if (L.newmax > G.newmax) G.newmax = L.newmax;
        if (L.dmax > G.dmax) { G.dmax = L.dmax; G.dmax_n = L.dmax_n; }
        if (L.jminmax > G.jminmax) { G.jminmax = L.jminmax; G.jminmax_rho = L.jminmax_rho; }
        G.settled += L.settled; G.direct += L.direct; G.dbad += L.dbad; G.bad += L.bad;
        sprintf(q, "%s/global.bin", DIR); sprintf(tmp, "%s.tmp", q); { FILE *f = fopen(tmp, "wb"); fwrite(&G, sizeof G, 1, f); fclose(f); rename(tmp, q); }
        printf("digits %2d: settled %lld, still open %lld, longest chain here %d (overall %d), largest j_min %lld, direct runs %lld (problems %lld, longest chain %d at n = %lld), class problems %lld, largest jump so far %lld (n = %lld)\n",
               k, L.settled, L.open2, L.newmax, G.newmax, L.jminmax, L.direct, L.dbad, L.dmax, L.dmax_n, L.bad, G.Jmax, G.Jmax_n);
        fflush(stdout);
        pth(p, "open_%d.ok", k + 1, 0); fclose(fopen(p, "w"));
        pth(p, "open_%d.bin", k, 0); unlink(p); pth(p, "open_%d.ok", k, 0); unlink(p);
        for (int w = 0; w < 2; w++) for (int c = 0; nc * w / 2 + (long long)c * CH < nc * (w + 1) / 2; c++) { sprintf(p, "%s/nx_%d_%d_%d.bin", DIR, k, w, c); unlink(p); sprintf(p, "%s/st_%d_%d_%d.bin", DIR, k, w, c); unlink(p); }
    }
    { const char *ph[3] = {"gap", "shift", "packet"}, *nmT = "GMWB"; printf("closest approaches so far:\n");
      for (int a = 0; a < 3; a++) for (int x = 0; x < 4; x++) for (int y = 0; y < 4; y++)
        if (G.ms[a][x][y] < (1LL << 62)) printf("  %s %c%c min %lld (n=%lld)\n", ph[a], nmT[x], nmT[y], G.ms[a][x][y], G.msn[a][x][y]); }
    printf("totals: settled classes %lld, direct runs %lld, problems %lld/%lld, largest j_min %lld, largest jump %lld, longest chain %d\n", G.settled, G.direct, G.dbad, G.bad, G.jminmax, G.Jmax, G.newmax);
    return 0;
}
