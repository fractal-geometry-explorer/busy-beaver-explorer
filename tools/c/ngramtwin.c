/* ngramtwin.c: a certificate that NGramCPS with window widths NL, NR fails on a machine, from a "twin" tape.
 *
 *   ngramtwin MACHINE NL NR TAPEFILE STEPS HALTSTEPS
 *
 * TAPEFILE holds a configuration X: a line "STATE HEAD" (state letter, head index into the cell string) and a line of
 * cells (0/1; every cell outside the string is 0).
 *
 * The check.  Let C, L, R be the closed sets NGramCPS builds (tools/c/ngramcps.c, without stopping at halts).  They
 * contain every local configuration of the run from blank tape, every left window the run has when it steps right,
 * and every right window it has when it steps left (by induction on the run; at a position never visited the window
 * is blank, which L and R contain from the start).  Call a configuration X "covered" if its local configuration is in
 * C, its left window at every position p left of the head is in L and its right window at every position right of the
 * head is in R.  One step of the machine keeps X covered: stepping right, the old left window goes into L, and the new
 * right window is X's right window one cell further right, which is in R and agrees with the known cells, so the new
 * local configuration is one of those the decider adds; stepping left is the mirror image.  So if X is covered and the
 * machine halts from X, C contains a halting local configuration and the decider cannot answer NONHALT.
 *
 * This program checks that X is covered using only the run from blank tape: it collects the windows X needs (its
 * local configuration, its left windows, its right windows, exactly, as strings), runs the machine STEPS steps from
 * blank tape and marks each needed window found when the run shows it (local configurations at any step, left
 * windows at steps to the right, right windows at steps to the left; rolling hashes find candidates, which are then
 * compared cell by cell).  Then it runs the machine from X for at most HALTSTEPS steps.  If every needed window is
 * found and X halts, NGramCPS(NL, NR) fails on the machine: "CERTIFIED".  Windows not found are listed (the first
 * few), with their position in X.
 */
#include "tm.h"

typedef unsigned long long u64;
#define B1 0x9e3779b97f4a7c15ULL   /* odd: invertible mod 2^64 */

static int NL, NR;
typedef struct { u64 h; int side, need, found, pos; char *cells; } need_t;   /* side 0 left, 1 right, 2 local */
static need_t *nd; static int nn, ncap;
/* small open-addressing table hash -> first need index, chained */
static int *tab, *chain; static int tcap;

static u64 inv(u64 a) { u64 x = a; for (int i = 0; i < 6; i++) x *= 2 - a * x; return x; }
static u64 POW_L, POW_R, INV;

/* window hash: cells c[0..n-1] near first: sum c_i * B^i (+1 so zeros count) */
static u64 whash(const char *c, int n) { u64 h = 0, p = 1; for (int i = 0; i < n; i++) { h += (u64)(c[i] + 1) * p; p *= B1; } return h; }
static u64 lkey(u64 hl, int st, int m, u64 hr) { return hl * 0x2545F4914F6CDD1DULL ^ (hr + 0x632BE59BD9B4E019ULL * (u64)(st * 2 + m + 1)); }

static int find(u64 h, int side, const char *c, int n, int st, int m) {
    for (int i = tab[(h ^ (h >> 29)) & (tcap - 1)]; i >= 0; i = chain[i]) {
        need_t *x = &nd[i];
        if (x->h != h || x->side != side) continue;
        if (side < 2) { if (!memcmp(x->cells, c, n)) return i; }
        else if (x->cells[0] == st && x->cells[1] == m && !memcmp(x->cells + 2, c, NL + NR)) return i;
    }
    return -1;
}
static void add_need(u64 h, int side, const char *c, int len, int pos) {
    int st = side == 2 ? c[0] : 0, m = side == 2 ? c[1] : 0;
    if (find(h, side, side == 2 ? c + 2 : c, len, st, m) >= 0) return;
    if (nn == ncap) { ncap = ncap ? 2 * ncap : 1024; nd = realloc(nd, ncap * sizeof(need_t)); chain = realloc(chain, ncap * sizeof(int)); }
    need_t *x = &nd[nn]; x->h = h; x->side = side; x->found = 0; x->pos = pos;
    int L = side == 2 ? 2 + NL + NR : len;
    x->cells = malloc(L); memcpy(x->cells, c, L);
    int b = (int)((h ^ (h >> 29)) & (tcap - 1)); chain[nn] = tab[b]; tab[b] = nn; nn++;
}

static int cell(const char *s, long len, long p) { return (p >= 0 && p < len) ? s[p] - '0' : 0; }

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: ngramtwin MACHINE NL NR TAPEFILE STEPS HALTSTEPS\n"); return 1; }
    tm_machine M; if (tm_parse(argv[1], &M)) { fprintf(stderr, "bad machine\n"); return 1; }
    NL = atoi(argv[2]); NR = atoi(argv[3]);
    long long steps = atoll(argv[5]), hsteps = atoll(argv[6]);
    FILE *f = fopen(argv[4], "r"); if (!f) { perror(argv[4]); return 1; }
    char stc; long head; if (fscanf(f, " %c %ld", &stc, &head) != 2) { fprintf(stderr, "bad tape file\n"); return 1; }
    char *s = malloc(1 << 26); if (fscanf(f, " %67108863s", s) != 1) { fprintf(stderr, "bad tape file\n"); return 1; }
    fclose(f);
    long len = (long)strlen(s); int st0 = stc - 'A';
    POW_L = 1; for (int i = 0; i < NL - 1; i++) POW_L *= B1;
    POW_R = 1; for (int i = 0; i < NR - 1; i++) POW_R *= B1;
    INV = inv(B1);
    tcap = 1 << 20; tab = malloc(tcap * sizeof(int)); memset(tab, 0xff, tcap * sizeof(int));

    /* the windows X needs: left windows at p < head down to the first all-blank one, right windows at p > head */
    char *w = malloc(NL + NR + 2);
    for (long p = head - 1; p >= -1 - NL; p--) {
        for (int i = 0; i < NL; i++) w[i] = (char)cell(s, len, p - 1 - i);
        add_need(whash(w, NL), 0, w, NL, (int)p);
    }
    for (long p = head + 1; p <= len + NR; p++) {
        for (int i = 0; i < NR; i++) w[i] = (char)cell(s, len, p + 1 + i);
        add_need(whash(w, NR), 1, w, NR, (int)p);
    }
    {   /* the local configuration */
        char *c = malloc(2 + NL + NR); c[0] = (char)st0; c[1] = (char)cell(s, len, head);
        for (int i = 0; i < NL; i++) c[2 + i] = (char)cell(s, len, head - 1 - i);
        for (int i = 0; i < NR; i++) c[2 + NL + i] = (char)cell(s, len, head + 1 + i);
        u64 hl = whash(c + 2, NL), hr = whash(c + 2 + NL, NR);
        add_need(lkey(hl, c[0], c[1], hr), 2, c, NL + NR, (int)head);
    }
    int nneed[3] = {0, 0, 0}; for (int i = 0; i < nn; i++) nneed[nd[i].side]++;
    /* the blank windows are in L and R from the start */
    memset(w, 0, NL + NR + 2);
    { int i = find(whash(w, NL), 0, w, NL, 0, 0); if (i >= 0) nd[i].found = 1; i = find(whash(w, NR), 1, w, NR, 0, 0); if (i >= 0) nd[i].found = 1; }

    /* the run from blank tape, with rolling hashes of the two windows */
    tm_tape t; tm_tape_init(&t, 1 << 22); int st = 0;
    u64 hl = whash(w, NL), hr = whash(w, NR);   /* blank */
    long long k;
    for (k = 0; k < steps; k++) {
        int m = tm_get(&t, t.head);
        u64 lk = lkey(hl, st, m, hr);
        for (int j = tab[(lk ^ (lk >> 29)) & (tcap - 1)]; j >= 0; j = chain[j]) {
            need_t *x = &nd[j];
            if (x->found || x->side != 2 || x->h != lk || x->cells[0] != st || x->cells[1] != m) continue;
            int ok = 1;
            for (int q = 0; q < NL && ok; q++) ok = x->cells[2 + q] == tm_get(&t, t.head - 1 - q);
            for (int q = 0; q < NR && ok; q++) ok = x->cells[2 + NL + q] == tm_get(&t, t.head + 1 + q);
            if (ok) x->found = 1;
        }
        int ns = M.s[st][m];
        if (ns < 0) break;
        int wr = M.w[st][m], d = M.d[st][m];
        int side = d > 0 ? 0 : 1; u64 hh = d > 0 ? hl : hr; int n = d > 0 ? NL : NR;
        for (int j = tab[(hh ^ (hh >> 29)) & (tcap - 1)]; j >= 0; j = chain[j]) {
            need_t *x = &nd[j];
            if (x->found || x->side != side || x->h != hh) continue;
            int ok = 1;
            for (int q = 0; q < n && ok; q++) ok = x->cells[q] == tm_get(&t, d > 0 ? t.head - 1 - q : t.head + 1 + q);
            if (ok) x->found = 1;
        }
        /* update the hashes: stepping right, the left window gains the written cell near and loses its far cell;
           the right window loses its near cell (now the head) and gains a far cell */
        if (d > 0) {
            int far = tm_get(&t, t.head - NL);
            hl = (hl - (u64)(far + 1) * POW_L) * B1 + (u64)(wr + 1);
            int near = tm_get(&t, t.head + 1), nf = tm_get(&t, t.head + 1 + NR);
            hr = (hr - (u64)(near + 1)) * INV + (u64)(nf + 1) * POW_R;
        } else {
            int far = tm_get(&t, t.head + NR);
            hr = (hr - (u64)(far + 1) * POW_R) * B1 + (u64)(wr + 1);
            int near = tm_get(&t, t.head - 1), nf = tm_get(&t, t.head - 1 - NL);
            hl = (hl - (u64)(near + 1)) * INV + (u64)(nf + 1) * POW_L;
        }
        tm_step(&M, &t, &st);
    }
    int found[3] = {0, 0, 0}; for (int i = 0; i < nn; i++) found[nd[i].side] += nd[i].found;
    printf("widths %d %d\nreal_steps %lld\nreal_width %lld\n", NL, NR, k, t.hi - t.lo + 1);
    printf("left_windows_needed %d found %d\nright_windows_needed %d found %d\nlocal_config_found %d\n",
           nneed[0], found[0], nneed[1], found[1], found[2]);
    int shown = 0;
    for (int i = 0; i < nn && shown < 5; i++) if (!nd[i].found) {
        shown++;
        printf("missing %s at %d: ", nd[i].side == 0 ? "left window" : nd[i].side == 1 ? "right window" : "local config", nd[i].pos);
        int n = nd[i].side == 0 ? NL : nd[i].side == 1 ? NR : NL + NR, o = nd[i].side == 2 ? 2 : 0;
        if (nd[i].side == 0) for (int q = n - 1; q >= 0; q--) putchar('0' + nd[i].cells[q]);
        else for (int q = 0; q < n; q++) putchar('0' + nd[i].cells[o + q]);
        putchar('\n');
    }
    /* run X */
    tm_tape x; tm_tape_init(&x, 4 * len + (1 << 20));
    for (long p = 0; p < len; p++) x.c[p + x.off] = (unsigned char)(s[p] - '0');
    x.head = head; x.lo = 0; x.hi = len - 1; int xs = st0, halted = 0;
    long long ran = tm_run(&M, &x, &xs, hsteps, &halted);
    printf("twin_halts %d\ntwin_steps %lld\n", halted, ran);
    int covered = found[0] == nneed[0] && found[1] == nneed[1] && found[2] == 1;
    printf("covered %d\nverdict %s\n", covered, covered && halted ? "CERTIFIED" : "NOT_CERTIFIED");
    return 0;
}
