/* walker: a hybrid simulator of 1RB0LD_1RC1RE_1LA0RA_1LE1LC_1RF1RC_---1RA (see ../README.md).
 *
 * At a sweep start the head is in state C on the blank cell right of the tape, and the tape is a sequence of groups
 * 1^m 0, then 1^t (t = 2 normally).  Items (x, m): x groups 110, then one group 1^m 0 with m != 2; the tail: q groups
 * 110, then 1^t.  Regular sweeps (t = 2, last item (x, m), m != 1) follow the walker rule
 *     m >= 4, m != 5:  (x, m-3), q+2          m = 5:  the item dissolves, q' = q + x + 3
 *     m = 3, x >= 1:   (x-1, 6), q+1          m = 3, x = 0:  (y, m') (0, 3) -> (y, m'+4), q+1
 * each in 10q + 23 steps; a walker phase (x, 3) -> (0, 3) (2x sweeps, q -> q + 3x) is applied at once.  Every other
 * sweep (an "event": last item (x, 1), t != 2, no items) is run cell by cell.
 *
 *   walker MAX_STEPS [1: log events | 2: every sweep start, no phase jumps]       from the sweep start at step 49: 1 0 (110)^2 1 1 C>
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef long long ll;
typedef __int128 i128;
#define MAXI 100000
static ll X[MAXI]; static int Mv[MAXI]; static int L; static ll Q; static int Tt;

static void print128(FILE *f, i128 x) {
    char b[64]; int k = 0; if (x == 0) { fputc('0', f); return; }
    while (x > 0) { b[k++] = '0' + (int)(x % 10); x /= 10; } while (k) fputc(b[--k], f);
}
static void pr(FILE *f) {
    fprintf(f, "[");
    for (int i = 0; i < L; i++) fprintf(f, "%s(%lld,%d)", i ? "," : "", X[i], Mv[i]);
    fprintf(f, "] q=%lld t=%d", Q, Tt);
}

/* transition table: state*2+symbol -> write, move(+1/-1), next; next = -1 halts */
static const int TW[12] = {1,0, 1,1, 1,0, 1,1, 1,1, 0,1};
static const int TM_[12] = {1,-1, 1,1, -1,1, -1,-1, 1,1, 0,1};
static const int TN[12] = {1,3, 2,4, 0,0, 4,2, 5,2, -1,0};

static unsigned char *tape; static ll cap;

/* run one sweep cell by cell; returns steps, or -1 on a halt (steps in *hs) */
static ll event(ll *hs) {
    ll n = 0;
    for (int i = 0; i < L; i++) n += 3 * X[i] + Mv[i] + 1;
    n += 3 * Q + Tt;
    ll need = n + 2 * 4096;
    if (need > cap) { cap = need * 2; tape = realloc(tape, cap); if (!tape) { fprintf(stderr, "oom\n"); exit(3); } }
    memset(tape, 0, cap);
    ll p = 4096;
    for (int i = 0; i < L; i++) {
        for (ll k = 0; k < X[i]; k++) { tape[p++] = 1; tape[p++] = 1; tape[p++] = 0; }
        for (int k = 0; k < Mv[i]; k++) tape[p++] = 1;
        tape[p++] = 0;
    }
    for (ll k = 0; k < Q; k++) { tape[p++] = 1; tape[p++] = 1; tape[p++] = 0; }
    for (int k = 0; k < Tt; k++) tape[p++] = 1;
    ll pos = p, hi = p, steps = 0; int st = 2;
    for (;;) {
        int sym = tape[pos], k = st * 2 + sym;
        if (TN[k] < 0) { *hs = steps; return -1; }
        tape[pos] = TW[k]; pos += TM_[k]; st = TN[k]; steps++;
        if (pos < 1) { fprintf(stderr, "left edge\n"); exit(4); }
        if (pos > hi) {
            hi = pos;
            if (pos + 2 >= cap) { fprintf(stderr, "right edge\n"); exit(4); }
            if (st == 2 && tape[pos] == 0) break;
        }
    }
    /* parse */
    ll lo = 0; while (tape[lo] == 0) lo++;
    L = 0; ll x = 0; int m = 0;
    for (ll i = lo; i < pos; i++) {
        if (tape[i]) m++;
        else {
            if (m == 2) x++;
            else { if (L >= MAXI) { fprintf(stderr, "items\n"); exit(3); } X[L] = x; Mv[L] = m; L++; x = 0; }
            m = 0;
        }
    }
    Q = x; Tt = m;
    return steps;
}

int main(int argc, char **argv) {
    double maxs = argc > 1 ? atof(argv[1]) : 1e12; int log = argc > 2 ? atoi(argv[2]) : 0;
    /* step 49: 1 0 (110)^2 1 1 C>  -> items [(0,1)], q = 2, t = 2 */
    L = 1; X[0] = 0; Mv[0] = 1; Q = 2; Tt = 2;
    i128 T = 49; ll sweeps = 0, events = 0, phases = 0, carries = 0;
    while ((double)T < maxs) {
        int last = L - 1;
        if (Tt == 2 && L >= 1 && Mv[last] != 1) {
            ll x = X[last]; int m = Mv[last];
            if (log == 2) { printf("S "); print128(stdout, T); printf(" "); pr(stdout); printf("\n"); }
            if (m == 3 && x >= 1 && log != 2) {         /* walker phase: x pairs of sweeps */
                T += (i128)20 * Q * x + (i128)30 * x * (x - 1) + (i128)56 * x;
                Q += 3 * x; X[last] = 0; sweeps += 2 * x; phases++;
                continue;
            }
            T += (i128)10 * Q + 23; sweeps++;
            if (m == 3 && x >= 1) { X[last] = x - 1; Mv[last] = 6; Q += 1; }
            else if (m == 3) {                    /* x = 0: merge with the previous item */
                if (L < 2) { fprintf(stderr, "merge without a previous item\n"); return 5; }
                Mv[last - 1] += 4; L--; Q += 1;
            } else if (m == 5) {
                Q += x + 3; L--;
            } else {
                Mv[last] = m - 3; Q += 2;
            }
            continue;
        }
        if (log != 2 && Tt == 2 && L >= 1 && Mv[L - 1] == 1 && X[L - 1] >= Q / 4 + 1) {
            /* a shallow carry: q = 4k + r */
            ll k = Q / 4; int r = (int)(Q % 4);
            if (log == 1) { printf("carry sweep %lld step ", sweeps); print128(stdout, T); printf(" (%lld,1) q=%lld\n", X[L - 1], Q); }
            T += (i128)50 * k * k + (r < 2 ? (i128)88 * k + 28 : (i128)138 * k + 82) + (r % 2 ? 7 : 0);
            X[L - 1] -= k + 1; Mv[L - 1] = r < 2 ? 6 : 3;
            Q = 5 * k + (r >= 2 ? 3 : 0); Tt = r % 2 ? 6 : 2;
            sweeps++; carries++;
            continue;
        }
        if (log != 2 && Tt == 6 && L >= 1) {
            /* the tail becomes an item: ... 1^6 C>  ->  ... (q, 3) 1 1 0 1 1 C> */
            if (L >= MAXI) { fprintf(stderr, "items\n"); return 3; }
            X[L] = Q; Mv[L] = 3; L++; Q = 1; Tt = 2; T += 13; sweeps++;
            continue;
        }
        ll hs = 0;
        if (log == 2) { printf("S "); print128(stdout, T); printf(" "); pr(stdout); printf("\n"); }
        else if (log) { printf("event sweep %lld step ", sweeps); print128(stdout, T); printf(" "); pr(stdout); printf("\n"); fflush(stdout); }
        ll s = event(&hs);
        if (s < 0) { printf("HALT at step "); print128(stdout, T + hs + 1); printf("\n"); return 0; }
        T += s; sweeps++; events++;
        if (log == 1) { printf("  -> "); pr(stdout); printf("\n"); }
    }
    printf("END step "); print128(stdout, T); printf(" (%.4e) sweeps %lld carries %lld deep-events %lld phases %lld items %d ", (double)T, sweeps, carries, events, phases, L);
    pr(stdout); printf("\n");
    return 0;
}
