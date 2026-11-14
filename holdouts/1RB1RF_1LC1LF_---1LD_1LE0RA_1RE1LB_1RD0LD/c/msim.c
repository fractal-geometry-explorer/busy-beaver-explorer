/* msim: an exact macro simulator for a two-symbol machine from blank tape.
 *
 *   msim MACHINE MAXEXP [B [CHECK [J]]]        (CHECK -1: none; J: with linear cycle jumps, see below)
 *
 * The tape is cut into blocks of B cells (default 3) on a fixed grid and stored run-length coded on two stacks (block
 * value, count).  The head is always between two blocks, moving in a direction; entering a block it runs the plain
 * machine inside that block and the block behind it until it leaves the two (a table, computed once per state, pair of
 * blocks and side).  If it leaves on the far side in the state it entered and the block now behind it equals the block
 * that was behind it before, the whole run of equal blocks in front is crossed at once (steps = count * steps of one).
 * Nothing else is accelerated, so every step count is exact.  Stops at a halt or at 10^MAXEXP steps; prints the
 * tape (blocks as bit strings, left to right) at the step counts 1, 2, 5 * 10^k and at the end.
 * With CHECK (a step count), it stops at the first block crossing at or after CHECK steps and prints
 * "CHECK steps state head ones hash": the head's cell relative to the leftmost 1, the number of 1s and a hash of the cells
 * between the extreme 1s, for comparison with the plain machine (chk.c). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 u128; typedef long long ll;
typedef struct { int v; ll c; } Tok;
typedef struct { Tok *t; ll n, cap; } Stk;
static void push(Stk *s, int v, ll c) {
    if (s->n == 0 && v == 0) return;
    if (s->n && s->t[s->n - 1].v == v) { s->t[s->n - 1].c += c; return; }
    if (s->n == s->cap) { s->cap = s->cap ? 2 * s->cap : 1024; s->t = realloc(s->t, sizeof(Tok) * s->cap); }
    s->t[s->n].v = v; s->t[s->n].c = c; s->n++;
}
static int W[6][2], D[6][2], S[6][2], B = 3;
typedef struct { int nu, nv, ndir, nst; ll k; int done; } Tr;   /* ndir 0: halt after k steps (counting the halting one) */
static Tr *T;
/* the head enters block v (in front) with block u behind it; the plain machine runs inside the two blocks until it leaves them */
static Tr *tr(int st, int u, int v, int dir) {
    Tr *r = &T[((((size_t)st << B) | u) << B | v) * 2 + (dir > 0)];
    if (r->done) return r;
    int cell[32], lo = dir > 0 ? u : v, hi = dir > 0 ? v : u;
    for (int i = 0; i < B; i++) { cell[i] = (lo >> (B - 1 - i)) & 1; cell[B + i] = (hi >> (B - 1 - i)) & 1; }
    int p = dir > 0 ? B : B - 1; ll k = 0; int s = st;
    for (;;) {
        int b = cell[p];
        if (S[s][b] < 0) { r->ndir = 0; r->k = k + 1; break; }
        cell[p] = W[s][b]; int d = D[s][b]; s = S[s][b]; p += d; k++;
        if (p < 0 || p >= 2 * B) { r->ndir = d; r->k = k; break; }
        if (k > 100000000) { fprintf(stderr, "loop inside a block\n"); exit(1); }
    }
    int nlo = 0, nhi = 0; for (int i = 0; i < B; i++) { nlo = 2 * nlo + cell[i]; nhi = 2 * nhi + cell[B + i]; }
    r->nst = s; r->nu = dir > 0 ? nlo : nhi; r->nv = dir > 0 ? nhi : nlo; r->done = 1; return r;
}
static void pr128(u128 x) { char b[64]; int i = 63; b[i] = 0; if (!x) { putchar('0'); return; } while (x) { b[--i] = '0' + (int)(x % 10); x /= 10; } fputs(b + i, stdout); }
static Stk L, R;
/* ---- linear cycle jumps (option J) ----
 * Sample points: the head turning from right to left after it has crossed at least one run at once.  If the last
 * four samples a period p apart have the same state and the same block values, the counts moved by the same vector d
 * each time, the steps of the three cycles are in arithmetic progression and each cycle took the same number m of
 * macro steps, and every count that moves is at least m + 4 at all four, then the cycle repeats: inside a cycle a
 * count changes by at most 1 per macro step apart from whole runs being moved or merged, so the tests the simulator
 * makes on counts (more than one copy left? none left?) come out the same for all larger counts, the end of a cycle is
 * an affine function of the counts and so is its step count; an affine map that is a translation by d at two points
 * of a line in direction d is that translation on the whole line.  So k further cycles add k d to the counts and
 * k s + e k (k-1) / 2 steps (s the steps of the next cycle, e the common difference), as long as the moving counts stay
 * at least m + 4. */
#define HIST 24
#define MAXT 512
typedef __int128 i128;
static struct { int st; ll n, nl; int v[MAXT]; ll c[MAXT]; u128 steps; unsigned long long ms; int ok; } H[HIST];
static long hn = 0; static int sample = 0, chained = 0; static unsigned long long njumps = 0; static int JUMP = 0;
static void prtok(int v, ll c) { for (int i = B - 1; i >= 0; i--) putchar('0' + ((v >> i) & 1)); if (c > 1) printf("^%lld", c); putchar(' '); }
static void prtape(int st, int dir) {
    for (ll i = 0; i < L.n; i++) prtok(L.t[i].v, L.t[i].c);
    printf(dir > 0 ? "%c> " : "<%c ", 'A' + st);
    for (ll i = R.n - 1; i >= 0; i--) prtok(R.t[i].v, R.t[i].c);
    printf("\n");
}
int main(int argc, char **argv) {
    const char *m = argv[1]; int maxexp = atoi(argv[2]); if (argc > 3) B = atoi(argv[3]);
    double check = argc > 4 ? atof(argv[4]) : -1; JUMP = argc > 5 && argv[5][0] == 'J';
    for (int s = 0; s < 6; s++) for (int b = 0; b < 2; b++) { const char *p = m + 7 * s + 3 * b; if (p[0] == '-') { S[s][b] = -1; continue; } W[s][b] = p[0] - '0'; D[s][b] = p[1] == 'R' ? 1 : -1; S[s][b] = p[2] - 'A'; }
    T = calloc((size_t)6 << (2 * B + 1), sizeof(Tr));
    u128 steps = 0, lim = 1, mark = 1; for (int i = 0; i < maxexp; i++) lim *= 10;
    int mi = 0; u128 base = 1; unsigned long long msteps = 0;
    int st = 0, dir = 1;
    while (steps < lim) {
        if (check >= 0 && (double)steps >= check) {
            /* expand */
            ll nl = 0, nr = 0; for (ll i = 0; i < L.n; i++) nl += L.t[i].c; for (ll i = 0; i < R.n; i++) nr += R.t[i].c;
            ll n = (nl + nr) * B; unsigned char *c = malloc(n + 1); ll q = 0;
            for (ll i = 0; i < L.n; i++) for (ll j = 0; j < L.t[i].c; j++) for (int b = B - 1; b >= 0; b--) c[q++] = (L.t[i].v >> b) & 1;
            ll head = dir > 0 ? q : q - 1;
            for (ll i = R.n - 1; i >= 0; i--) for (ll j = 0; j < R.t[i].c; j++) for (int b = B - 1; b >= 0; b--) c[q++] = (R.t[i].v >> b) & 1;
            ll a = 0, z = n - 1; while (a < n && !c[a]) a++; while (z >= 0 && !c[z]) z--;
            unsigned long long h = 0, ones = 0; for (ll i = a; i <= z; i++) { h = h * 1000003ULL + c[i]; ones += c[i]; }
            printf("CHECK "); pr128(steps); printf(" %c %lld %llu %llu\n", 'A' + st, head - a, ones, h); return 0;
        }
        if (steps >= mark) { printf("@ "); pr128(steps); printf(" msteps %llu jumps %llu tokens %lld : ", msteps, njumps, L.n + R.n); if (L.n + R.n < 150) prtape(st, dir); else printf("\n"); fflush(stdout);
            while (mark <= steps) { mi = (mi + 1) % 3; if (mi == 0) base *= 10; mark = base * (mi == 0 ? 1 : mi == 1 ? 2 : 5); } }
        if (JUMP && sample) { sample = 0; chained = 0;
            ll NT = L.n + R.n;
            int cur = hn % HIST; hn++;
            H[cur].ok = NT <= MAXT; H[cur].st = st; H[cur].n = NT; H[cur].nl = L.n; H[cur].steps = steps; H[cur].ms = msteps;
            if (H[cur].ok) for (ll i = 0; i < NT; i++) { Tok *t = i < L.n ? &L.t[i] : &R.t[i - L.n]; H[cur].v[i] = t->v; H[cur].c[i] = t->c; }
            for (int p = 1; H[cur].ok && p <= 5 && 3 * p < HIST && hn > 3 * p; p++) {
                int i1 = (cur - p + HIST) % HIST, i2 = (cur - 2 * p + HIST) % HIST, i3 = (cur - 3 * p + HIST) % HIST, good = 1;
                int idx[4] = { cur, i1, i2, i3 };
                for (int j = 1; j < 4 && good; j++) { if (!H[idx[j]].ok || H[idx[j]].st != st || H[idx[j]].n != NT || H[idx[j]].nl != L.n) good = 0;
                    else for (ll i = 0; i < NT; i++) if (H[idx[j]].v[i] != H[cur].v[i]) { good = 0; break; } }
                if (!good) continue;
                unsigned long long m = H[cur].ms - H[i1].ms;
                if (H[i1].ms - H[i2].ms != m || H[i2].ms - H[i3].ms != m) continue;
                i128 s1 = (i128)(H[cur].steps - H[i1].steps), s0 = (i128)(H[i1].steps - H[i2].steps), sm = (i128)(H[i2].steps - H[i3].steps), e = s1 - s0;
                if (s0 - sm != e) continue;
                ll k = -1, M = (ll)m + 4;
                for (ll i = 0; i < NT && good; i++) { ll d = H[cur].c[i] - H[i1].c[i];
                    if (H[i1].c[i] - H[i2].c[i] != d || H[i2].c[i] - H[i3].c[i] != d) { good = 0; break; }
                    if (d == 0) continue;
                    for (int j = 0; j < 4; j++) if (H[idx[j]].c[i] < M) good = 0;
                    if (d < 0 && good) { ll kk = (H[cur].c[i] - M) / (-d); if (k < 0 || kk < k) k = kk; } }
                if (!good || k < 2) continue;
                /* do not pass the step limit or the check point */
                u128 room = (check >= 0 && (u128)check > steps) ? (u128)check - steps : (lim > steps ? lim - steps : 0);
                i128 sn = s1 + e;
                if (sn <= 0 || e < 0) continue;
                { ll lo = 0, hi = k; while (lo < hi) { ll mid = lo + (hi - lo + 1) / 2; u128 tot = (u128)mid * (u128)sn + (u128)e * ((u128)mid * (u128)(mid - 1) / 2); if (tot <= room) lo = mid; else hi = mid - 1; } k = lo; }
                if (k < 2) continue;
                for (ll i = 0; i < NT; i++) { Tok *t = i < L.n ? &L.t[i] : &R.t[i - L.n]; t->c += k * (H[cur].c[i] - H[i1].c[i]); }
                steps += (u128)k * (u128)sn + (u128)e * ((u128)k * (u128)(k - 1) / 2); njumps++; hn = 0;
                break;
            }
        }
        Stk *f = dir > 0 ? &R : &L, *bh = dir > 0 ? &L : &R; int v = 0, u = 0; ll c = 1;
        if (f->n) { v = f->t[f->n - 1].v; c = f->t[f->n - 1].c; }
        if (bh->n) { u = bh->t[bh->n - 1].v; if (--bh->t[bh->n - 1].c == 0) bh->n--; }
        Tr *r = tr(st, u, v, dir); msteps++;
        if (r->ndir == 0) { push(bh, u, 1); steps += r->k; printf("HALT "); pr128(steps); printf(" msteps %llu : ", msteps); prtape(st, dir); return 0; }
        if (r->ndir == dir && r->nst == st && r->nv == u && f->n && c > 1) {
            f->n--; steps += (u128)r->k * (u128)c; push(bh, r->nu, c); push(bh, u, 1); chained = 1;
        } else {
            if (f->n) { if (--f->t[f->n - 1].c == 0) f->n--; }
            steps += r->k; st = r->nst;
            if (r->ndir == dir) { push(bh, r->nu, 1); push(bh, r->nv, 1); }
            else { push(f, r->nv, 1); push(f, r->nu, 1); if (dir > 0 && chained) sample = 1; dir = r->ndir; }
        }
    }
    printf("RUNNING "); pr128(steps); printf(" msteps %llu : ", msteps); if (L.n + R.n < 400) prtape(st, dir); else printf("%lld tokens\n", L.n + R.n);
    return 0;
}
