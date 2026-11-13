/* mrun: exact macro simulator (blocks of K cells, runs crossed at once) for two-symbol machines from blank tape.
 *
 *   mrun MACHINE K MAX_STEPS [EVERY [SIDE]]
 *
 * Runs until MAX_STEPS (approximately: a run crossing may overshoot; the reported count is exact) or a halt.
 * Every EVERY-th time the head extends the tape (on SIDE L, R or LR) it prints "STEPS L|R CELLS  tape", the tape as
 * runs of K-cell blocks "bits^count", the head shown as "S>" (facing right) or "<S" (facing left) between blocks.
 * Final line: "halted STEPS" or "running STEPS", the width in cells, and the tape.
 * Steps follow the bbchallenge count (the halting transition counts).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long long ll;
static int W[6][2], MV[6][2], NX[6][2], HALT[6][2];
static int K;
typedef struct { int b; ll n; } run;
typedef struct { run *a; int n, cap; } stk;
static void push(stk *s, int b, ll n) {
    if (n <= 0) return;
    if (s->n && s->a[s->n-1].b == b) { s->a[s->n-1].n += n; return; }
    if (s->n == s->cap) { s->cap = s->cap ? 2*s->cap : 1024; s->a = realloc(s->a, s->cap*sizeof(run)); }
    s->a[s->n].b = b; s->a[s->n].n = n; s->n++;
}
/* cache: state(6) x block(2^K) x side(2) -> result */
typedef struct { int done, nb, ns, out, halted; ll steps; } res;
static res *cache;
/* block bits: bit i = cell i, cell 0 leftmost */
static res blk(int st, int b, int side) {
    res *r = &cache[(st*(1<<K)+b)*2+side];
    if (r->done) return *r;
    int pos = side ? K-1 : 0; ll k = 0; int s = st, bb = b;
    r->halted = 0;
    while (pos >= 0 && pos < K) {
        int c = (bb >> pos) & 1;
        k++;
        if (HALT[s][c]) { r->halted = 1; break; }
        if (W[s][c]) bb |= 1<<pos; else bb &= ~(1<<pos);
        pos += MV[s][c]; s = NX[s][c];
        if (k > 100000) { fprintf(stderr, "loop in block\n"); exit(2); }
    }
    r->done = 1; r->nb = bb; r->ns = s; r->out = pos < 0 ? 0 : 1; r->steps = k;
    return *r;
}
static stk L, R; /* L: blocks left of head, top nearest; R: right */
static void pblock(int b) { for (int i = 0; i < K; i++) putchar('0' + ((b>>i)&1)); }
static void ptape(int st, int facing) {
    for (int i = 0; i < L.n; i++) { pblock(L.a[i].b); if (L.a[i].n > 1) printf("^%lld", L.a[i].n); putchar(' '); }
    if (facing) printf("%c> ", 'A'+st); else printf("<%c ", 'A'+st);
    for (int i = R.n-1; i >= 0; i--) { pblock(R.a[i].b); if (R.a[i].n > 1) printf("^%lld", R.a[i].n); putchar(' '); }
    putchar('\n');
}
int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: mrun MACHINE K MAX_STEPS [EVERY [SIDE]]\n"); return 1; }
    const char *m = argv[1];
    for (int s = 0; s < 6; s++) for (int c = 0; c < 2; c++) {
        const char *t = m + 7*s + 3*c;
        if (t[0] == '-') { HALT[s][c] = 1; continue; }
        W[s][c] = t[0]-'0'; MV[s][c] = t[1]=='R' ? 1 : -1; NX[s][c] = t[2]-'A';
    }
    K = atoi(argv[2]); ll max = atoll(argv[3]); ll every = argc > 4 ? atoll(argv[4]) : 0;
    const char *side = argc > 5 ? argv[5] : "LR";
    int wantL = strchr(side,'L') != NULL, wantR = strchr(side,'R') != NULL;
    cache = calloc((size_t)6*(1<<K)*2, sizeof(res));
    int st = 0, facing = 1; /* head at left edge of first R block, facing right */
    ll steps = 0, cells = 0, ext = 0; int halted = 0;
    while (steps < max) {
        stk *f = facing ? &R : &L, *o = facing ? &L : &R;
        int b; ll n; int newcell = 0;
        if (f->n == 0) { b = 0; n = 1; newcell = 1; cells += K; push(f, 0, 1); }
        b = f->a[f->n-1].b; n = f->a[f->n-1].n;
        res r = blk(st, b, facing ? 0 : 1);
        if (r.halted) { steps += r.steps; halted = 1; break; }
        int far = facing ? 1 : 0;
        if (r.out == far && r.ns == st) {
            /* cross the whole run */
            f->n--; steps += r.steps * n; push(o, r.nb, n);
        } else {
            if (--f->a[f->n-1].n == 0) f->n--;
            steps += r.steps;
            if (r.out == far) push(o, r.nb, 1); else push(f, r.nb, 1);
            /* head now between: if it left on the far side it faces the next block onward; else it turns */
            facing = (r.out == far) ? facing : !facing;
            st = r.ns;
            if (newcell && every) {}
        }
        if (newcell) {
            ext++;
            if (every && ext % every == 0 && ((facing && wantR) || (!facing && wantL) || 1)) {
                int sideR = (f == &R);
                if ((sideR && wantR) || (!sideR && wantL)) { printf("%lld %c %lld ", steps, sideR ? 'R' : 'L', cells); ptape(st, facing); }
            }
        }
    }
    printf("%s %lld %lld ", halted ? "halted" : "running", steps, cells); ptape(st, facing);
    return 0;
}
