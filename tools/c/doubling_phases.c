/* doubling_phases.c: the phase maps `next` of lean/Phases.lean of the four "two blocks take turns doubling" machines,
   transcribed case by case; step counts from py/phasemap.py (for reporting only).
   Build: gcc -O2 -o doubling_phases tools/c/doubling_phases.c.  Checked against each machine's py/phasemap.py `nxt`
   (states and step counts) for the first 300,000 phases.
   usage: phases MACHINE_NO PHASES REPORT CKPT
   1 = 1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE   init a 0 0
   2 = 1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE   init r 0 2 (steps 2)
   3 = 1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE   init a 0 0
   4 = 1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE   init r 0 2 (steps 6)
   Kinds: E = e x z, Q = q m j t, A = a/r x y.  Halt: e x 0 or e x 1. */
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
typedef long long ll; typedef unsigned long long ull;
enum { E, Q, A };
typedef struct { int k; ll a, b, c; } Ph;
static int mach;
static ll mn(ll a, ll b) { return a < b ? a : b; }
#define CHK(v) do { if ((v) > (1LL << 61) || (v) < 0) { fprintf(stderr, "overflow\n"); exit(3); } } while (0)
/* returns 0 = halt; *s = steps of the phase (as in phasemap.py) */
static int next(Ph *p, long double *s) {
    ll x = p->a, y = p->b, t = p->c;
    if (p->k == E) {                      /* e x z (x = a, z = b) */
        if (y <= 1) return 0;
        *s = 2.0L * x + 3; p->k = Q; p->a = x; p->b = 0; p->c = y - 2; return 1;
    }
    if (p->k == Q) {
        ll m = x, j = y;
        if (m >= 1 && t >= 3) {
            ll b = mn(m, (t - 1) / 2);     /* min (m'+1) ((t'+2)/2) with m = m'+1, t = t'+3 */
            if (mach == 1 || mach == 3) { *s = 8.0L * ((long double)b * j + (long double)b * (b - 1) / 2) + 10.0L * b; p->a = m - b; p->b = j + b; p->c = t - 2 * b; }
            else { *s = 4.0L * ((long double)b * j + (long double)b * (b - 1)) + (mach == 2 ? 10.0L : 12.0L) * b; p->a = m - b; p->b = j + 2 * b; p->c = t - 2 * b; }
            CHK(p->b); return 1;
        }
        if (mach == 1 || mach == 3) {
            if (m == 0 && t >= 5) { *s = 16.0L * j + 27; p->k = E; p->a = 2 * j + 4; p->b = t - 4; return 1; }
            if (m == 0 && t == 4) { *s = 12.0L * j + 19; p->k = A; p->a = 0; p->b = 4 * j + 9; return 1; }
            if (m == 0 && t == 3) { *s = 12.0L * j + 17; p->k = A; p->a = 0; p->b = 4 * j + 7; return 1; }
            if (t == 2) { *s = 4.0L * j + 5; p->k = A; p->a = m; p->b = 4 * j + 6; return 1; }
            if (t == 1) { *s = 4.0L * j + 3; p->k = A; p->a = m; p->b = 4 * j + 4; return 1; }
            /* t == 0 */
            if (mach == 1) {
                if (m >= 1) { *s = 8.0L * j + 10; p->a = m - 1; p->b = 0; p->c = 4 * j + 2; return 1; }
                if (j == 0) { *s = 15; p->k = A; p->a = 0; p->b = 5; return 1; }
                *s = 8.0L * (j - 1) + 27; p->k = E; p->a = 2; p->b = 4 * (j - 1) + 4; return 1;
            } else {
                if (m >= 2) { *s = 8.0L * j + 10; p->a = m - 2; p->b = 0; p->c = 4 * j + 4; return 1; }
                if (m == 1) { *s = 8.0L * j + 19; p->k = E; p->a = 2; p->b = 4 * j + 2; return 1; }
                if (j == 0) { *s = 21; p->k = A; p->a = 0; p->b = 7; return 1; }
                *s = 8.0L * (j - 1) + 35; p->k = E; p->a = 3; p->b = 4 * (j - 1) + 4; return 1;
            }
        }
        ll k = j;
        if (mach == 2) {
            if (m == 0 && t >= 5) { *s = 8.0L * k + 27; p->k = E; p->a = k + 4; p->b = t - 4; return 1; }
            if (m == 0 && t == 4) { *s = 6.0L * k + 20; p->k = A; p->a = 0; p->b = 2 * k + 10; return 1; }
            if (m == 0 && t == 3) { *s = 6.0L * k + 18; p->k = A; p->a = 0; p->b = 2 * k + 8; return 1; }
            /* t <= 2: r m (2k + 3 + 2t) */
            *s = 2.0L * k + 2 + 2 * t; p->k = A; p->a = m; p->b = 2 * k + 3 + 2 * t; return 1;
        }
        /* mach 4 */
        if (m == 0 && t >= 5) { *s = 8.0L * k + 31; p->k = E; p->a = k + 4; p->b = t - 4; return 1; }
        if (m == 0 && t == 4) { *s = 6.0L * k + 23; p->k = A; p->a = 0; p->b = 2 * k + 8; return 1; }
        if (m == 0 && t == 3) { *s = 8.0L * k + 36; p->k = E; p->a = 1; p->b = 2 * k + 7; return 1; }
        if (t == 2) { *s = 2.0L * k + 7; p->k = A; p->a = m; p->b = 2 * k + 5; return 1; }
        if (t == 1) {
            if (m == 0) { *s = 4.0L * k + 17; p->k = E; p->a = 1; p->b = 2 * k + 4; return 1; }
            if (m == 1) { *s = 4.0L * k + 33; p->k = E; p->a = 3; p->b = 2 * k + 2; return 1; }
            *s = 4.0L * k + 18; p->a = m - 2; p->b = 1; p->c = 2 * k + 4; return 1;
        }
        if (m == 0) { *s = 4.0L * k + 13; p->k = E; p->a = 1; p->b = 2 * k + 2; return 1; }
        if (m == 1) {
            if (k == 0) { *s = 23; p->k = A; p->a = 0; p->b = 6; return 1; }
            *s = 4.0L * (k - 1) + 33; p->k = E; p->a = 3; p->b = 2 * (k - 1) + 2; return 1;
        }
        *s = 4.0L * k + 14; p->a = m - 2; p->b = 1; p->c = 2 * k + 2; return 1;
    }
    /* A: a/r x y */
    if (mach == 1) {
        if (x >= 1 && y >= 1) { *s = (y % 2 == 0) ? 2.0L * ((y - 2) / 2) + 9 : 2.0L * ((y - 1) / 2) + 8; p->k = Q; p->a = x - 1; p->b = 0; p->c = y; return 1; }
        if (y == 0 && x >= 1) { *s = 6; p->b = 2; return 1; }
        if (y == 0) { *s = 6; p->b = 2; return 1; }
        if (y == 1) { *s = 30; p->k = E; p->a = 2; p->b = 1; return 1; }
        if (y == 2) { *s = 14; p->b = 5; return 1; }
        if (y == 3) { *s = 19; p->k = E; p->a = 2; p->b = 1; return 1; }
        if (y == 4) { *s = 20; p->k = E; p->a = 2; p->b = 2; return 1; }
        *s = y - 5 + 21.0L; p->k = E; p->a = 2; p->b = y - 2; return 1;
    }
    if (mach == 2) {
        if (x == 0) { if (y == 0) { *s = 2; p->k = E; p->a = 0; p->b = 1; } else { *s = y - 1 + 3.0L; p->k = E; p->a = 0; p->b = y + 1; } return 1; }
        if (x == 1) {
            if (y == 0) { *s = 7; p->a = 0; p->b = 4; return 1; }
            if (y == 1) { *s = 10; p->a = 0; p->b = 6; return 1; }
            *s = y - 2 + 14.0L; p->k = E; p->a = 2; p->b = y - 1; return 1;
        }
        if (y == 0) { *s = 3; p->k = Q; p->a = x - 2; p->b = 1; p->c = 0; return 1; }
        *s = y - 1 + 4.0L; p->k = Q; p->a = x - 2; p->b = 0; p->c = y + 1; return 1;
    }
    if (mach == 3) {
        if (x >= 2) {
            if (y == 0) { *s = 7; p->k = Q; p->a = x - 2; p->b = 0; p->c = 2; return 1; }
            *s = (y % 2 == 0) ? 2.0L * ((y - 2) / 2) + 9 : 2.0L * ((y - 1) / 2) + 8; p->k = Q; p->a = x - 2; p->b = 0; p->c = y + 2; return 1;
        }
        if (x == 1) {
            if (y == 0) { *s = 12; p->a = 0; p->b = 5; return 1; }
            *s = (y % 2 == 0) ? 2.0L * ((y - 2) / 2) + 18 : 2.0L * ((y - 1) / 2) + 17; p->k = E; p->a = 2; p->b = y; return 1;
        }
        if (y == 0) { *s = 8; p->b = 4; return 1; }
        if (y == 1) { *s = 46; p->k = E; p->a = 3; p->b = 3; return 1; }
        if (y == 2) { *s = 20; p->b = 7; return 1; }
        if (y == 3) { *s = 27; p->k = E; p->a = 3; p->b = 1; return 1; }
        if (y == 4) { *s = 28; p->k = E; p->a = 3; p->b = 2; return 1; }
        *s = y - 5 + 29.0L; p->k = E; p->a = 3; p->b = y - 2; return 1;
    }
    /* mach 4 */
    if (x == 0) { if (y == 0) { *s = 11; p->k = E; p->a = 1; p->b = 1; } else { *s = y - 1 + 12.0L; p->k = E; p->a = 1; p->b = y + 1; } return 1; }
    if (x == 1) {
        if (y == 0) { *s = 32; p->k = E; p->a = 1; p->b = 5; return 1; }
        if (y == 1) { *s = 22; p->a = 0; p->b = 6; return 1; }
        if (y == 2) { *s = 29; p->k = E; p->a = 3; p->b = 1; return 1; }
        *s = y - 3 + 30.0L; p->k = E; p->a = 3; p->b = y - 1; return 1;
    }
    if (y == 0) { *s = 12; p->k = Q; p->a = x - 2; p->b = 1; p->c = 1; return 1; }
    *s = y - 1 + 13.0L; p->k = Q; p->a = x - 2; p->b = 1; p->c = y + 1; return 1;
}
int main(int argc, char **argv) {
    mach = atoi(argv[1]); ull N = strtoull(argv[2], 0, 10), Rp = strtoull(argv[3], 0, 10); const char *ck = argv[4];
    int trace = argc > 5 ? atoi(argv[5]) : 0;
    Ph p; long double steps; ull i = 0; ull nones = 0; ll lastones = -1; long double lastones_step = 0;
    FILE *in = fopen(ck, "r");
    if (in) { if (fscanf(in, "%llu %d %lld %lld %lld %Lf %llu %lld %Lf", &i, &p.k, &p.a, &p.b, &p.c, &steps, &nones, &lastones, &lastones_step) != 9) return 4; fclose(in); fprintf(stderr, "resumed at phase %llu\n", i); }
    else { p.k = A; p.a = 0; p.c = 0; if (mach == 1 || mach == 3) { p.b = 0; steps = 0; } else { p.b = 2; steps = mach == 2 ? 2 : 6; } }
    time_t t0 = time(0);
    for (; i < N; i++) {
        if (p.k != Q) p.c = 0;
        if (trace && i < (ull)trace) printf("%llu %c %lld %lld %lld %.0Lf\n", i, "eqa"[p.k], p.a, p.b, p.c, steps);
        if (p.k == A && p.a == 0) { nones++; lastones = p.b; lastones_step = steps; if (!trace) { printf("all-ones phase %llu: n = %lld at step %.6Le\n", i, p.b, steps); fflush(stdout); } }
        long double s = 0;
        if (!next(&p, &s)) {
            printf("HALT: phase %llu is e %lld %lld (step %.6Le)\n", i, p.a, p.b, steps);
            FILE *o = fopen("HALT_FOUND", "a"); fprintf(o, "mach %d phase %llu e %lld %lld\n", mach, i, p.a, p.b); fclose(o); return 1;
        }
        steps += s;
        if ((i + 1) % Rp == 0) {
            FILE *o = fopen("ck.tmp", "w"); fprintf(o, "%llu %d %lld %lld %lld %.30Le %llu %lld %.30Le\n", i + 1, p.k, p.a, p.b, p.c, steps, nones, lastones, lastones_step); fclose(o); rename("ck.tmp", ck);
            if (!trace) { printf("phase %llu: %c %lld %lld %lld, steps %.4Le, all-ones phases %llu (%lds)\n", i + 1, "eqa"[p.k], p.a, p.b, p.c, steps, nones, (long)(time(0) - t0)); fflush(stdout); }
        }
    }
    printf("done %llu phases, no halt; state %c %lld %lld %lld; steps %.6Le; all-ones phases %llu, last n = %lld at step %.4Le\n", i, "eqa"[p.k], p.a, p.b, p.c, steps, nones, lastones, lastones_step);
    return 0;
}
