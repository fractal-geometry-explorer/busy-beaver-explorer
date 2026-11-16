/* redmaps.c: exact iteration of the Lean-proved reduced maps of several BB(6) holdouts.
   usage: redmaps MAP STEPS REPORT CKPT [trace K]
   Build: gcc -O2 -o redmaps tools/c/redmaps.c -l:libgmp.so.10.  Each map is the Lean definition named below (re1: the
   closed form 3n - 2c_i + i + 3 of Phase1.lean `ph`, equal to it for every n).  Checked against the machines' own
   py/orbit.py for the first 30,000 steps.
   MAP: mapc (1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA, Map.lean mapc from (74,30))
        rb   (1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE, Round.lean next from (3,1,false))
        rc   (1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD, Macro.lean next from (p,3,0))
        re0  (1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE, Map.lean f from (2,1))
        re1  (1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE, closed form of Phase1.lean next from 1)
   The state is (x, y, flag); a checkpoint (step, flag, x, y in hex) is written every REPORT steps and resumed. */
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "gmp_decl.h"
static mpz_t x, y, d, t, u;
static int flag; static long long stp;
static const char *map;
static long minbits = 1L << 60; /* sentinel */ static long long minat = -1;
/* closeness of a halting decision: bits of the larger number minus bits of the halting difference d (largest gap
   seen after step 1000 is reported as minbits = that gap, i.e. "d had only that many fewer bits") */
static void gapnote(mpz_srcptr dd, long long k) {
    if (k < 1000) return;
    long bx = (long)mpz_sizeinbase(x, 2), by = (long)mpz_sizeinbase(y, 2), b = mpz_sgn(dd) ? (long)mpz_sizeinbase(dd, 2) : 0;
    long g = (bx > by ? bx : by) - b;
    if (minbits == (1L << 60) || g > minbits) { minbits = g; minat = k; }
}
static void note(long long k) { gapnote(d, k); }
/* returns 0 ok, 1 halt, 2 small */
static int step(void) {
    if (!strcmp(map, "mapc")) {           /* x = a, y = c */
        if (mpz_odd_p(x) || mpz_cmp_ui(x, 4) < 0) return 2;
        mpz_sub(d, y, x); note(stp);
        if (!mpz_odd_p(y)) {
            if (mpz_cmp_ui(y, 18) < 0 || mpz_cmp_ui(x, 6) < 0) return 2;
            if (mpz_cmp_si(d, 8) <= 0) { mpz_ui_sub(x, 12, d); mpz_mul_ui(y, y, 3); mpz_sub_ui(y, y, 6); return 0; }
            if (mpz_cmp_si(d, 12) <= 0) return 1;
            mpz_mul_ui(y, x, 3); mpz_add_ui(y, y, 27); mpz_sub_ui(x, d, 10); return 0;
        } else {
            if (mpz_cmp_ui(y, 5) < 0) return 2;
            if (mpz_cmp_si(d, -5) <= 0) { mpz_neg(x, d); mpz_sub_ui(x, x, 1); mpz_mul_ui(y, y, 3); mpz_add_ui(y, y, 6); return 0; }
            if (mpz_sgn(d) < 0) return 1;
            mpz_mul_ui(y, x, 3); mpz_add_ui(x, d, 3); return 0;
        }
    }
    if (!strcmp(map, "rb")) {             /* x = i, y = j, flag = J */
        mpz_sub(d, x, y); note(stp);
        if (mpz_sgn(d) == 0 || mpz_cmp_si(d, -1) == 0) return 1;
        if (mpz_cmp_si(d, 2) >= 0) { mpz_sub_ui(x, d, 1); mpz_mul_ui(y, y, 3); mpz_add_ui(y, y, flag ? 3 : 2); return 0; }
        if (mpz_cmp_si(d, 1) == 0) {
            if (!flag) { mpz_mul_ui(x, x, 3); mpz_sub_ui(x, x, 3); mpz_set_ui(y, 3); flag = 1; }
            else { mpz_mul_ui(x, x, 3); mpz_set_ui(y, 1); flag = 0; }
            return 0;
        }
        if (mpz_cmp_si(d, -2) == 0) {
            mpz_mul_ui(x, x, 3); mpz_add_ui(x, x, 3); if (!flag) mpz_set_ui(y, 1); else mpz_set_ui(y, 3); return 0;
        }
        mpz_mul_ui(y, x, 3); mpz_add_ui(y, y, flag ? 5 : 3); mpz_neg(x, d); mpz_sub_ui(x, x, 2); flag = !flag; return 0;
    }
    if (!strcmp(map, "rc")) {             /* flag = k (0 = p, 1 = q), x = u, y = v */
        mpz_sub(d, x, y); note(stp);
        if (mpz_sgn(d) == 0 || mpz_cmp_ui(d, 1) == 0) return 1;
        if (mpz_sgn(d) < 0) { mpz_mul_ui(x, x, 3); mpz_add_ui(x, x, flag ? 3 : 2); mpz_neg(y, d); mpz_sub_ui(y, y, 1); return 0; }
        mpz_mul_ui(x, y, 3); mpz_add_ui(x, x, flag ? 5 : 3); mpz_sub_ui(y, d, 2); flag = !flag; return 0;
    }
    if (!strcmp(map, "re0")) {            /* x = p, y = r */
        mpz_sub(d, y, x); mpz_sub_ui(t, d, 1); if (mpz_cmp_si(d, 2) < 0) gapnote(t, stp);
        if (mpz_cmp_si(d, 2) >= 0) { mpz_mul_ui(x, x, 2); mpz_add_ui(x, x, 2); mpz_sub_ui(y, d, 1); return 0; }
        if (mpz_cmp_si(d, 1) == 0) return 1;
        if (mpz_sgn(d) == 0) { mpz_mul_ui(y, x, 4); mpz_add_ui(y, y, 1); mpz_set_ui(x, 2); return 0; }
        mpz_neg(x, d); mpz_mul_ui(y, y, 4); mpz_add_ui(y, y, 2); return 0;
    }
    if (!strcmp(map, "re1")) {            /* x = n; c_i = 10*2^i - i - 7, c_{-1} = -1 */
        long L = (long)mpz_sizeinbase(x, 2), i = L - 5 < -1 ? -1 : L - 5;
#define CI(z, k) do { if ((k) < 0) mpz_set_si(z, -1); else { mpz_set_ui(z, 10); mpz_mul_2exp(z, z, (k)); mpz_sub_ui(z, z, (k) + 7); } } while (0)
        for (;;) { CI(t, i + 1); if (mpz_cmp(t, x) < 0) i++; else break; }
        for (;;) { CI(t, i); if (mpz_cmp(t, x) >= 0) i--; else break; }
        CI(t, i + 1); mpz_sub(d, t, x); note(stp);
        if (mpz_sgn(d) == 0) return 1;
        CI(t, i); mpz_mul_ui(x, x, 3); mpz_sub(x, x, t); mpz_sub(x, x, t); mpz_add_ui(x, x, i + 3); return 0;
    }
    fprintf(stderr, "unknown map\n"); exit(2);
}
static void save(const char *f) {
    char tmp[4096]; snprintf(tmp, sizeof tmp, "%s.tmp", f);
    FILE *o = fopen(tmp, "w"); fprintf(o, "%lld %d %ld %lld\n", stp, flag, minbits, minat);
    mpz_out_str(o, 16, x); fputc('\n', o); mpz_out_str(o, 16, y); fputc('\n', o); fclose(o); rename(tmp, f);
}
int main(int argc, char **argv) {
    map = argv[1]; long long N = atoll(argv[2]), R = atoll(argv[3]); const char *ck = argv[4];
    long long trace = argc > 6 ? atoll(argv[6]) : 0;
    mpz_init(x); mpz_init(y); mpz_init(d); mpz_init(t); mpz_init(u);
    FILE *in = fopen(ck, "r");
    if (in) { if (fscanf(in, "%lld %d %ld %lld", &stp, &flag, &minbits, &minat) != 4) return 3; mpz_inp_str(x, in, 16); mpz_inp_str(y, in, 16); fclose(in);
        fprintf(stderr, "resumed at %lld\n", stp); }
    else {
        stp = 0; flag = 0;
        if (!strcmp(map, "mapc")) { mpz_set_ui(x, 74); mpz_set_ui(y, 30); }
        else if (!strcmp(map, "rb")) { mpz_set_ui(x, 3); mpz_set_ui(y, 1); }
        else if (!strcmp(map, "rc")) { mpz_set_ui(x, 3); mpz_set_ui(y, 0); }
        else if (!strcmp(map, "re0")) { mpz_set_ui(x, 2); mpz_set_ui(y, 1); }
        else if (!strcmp(map, "re1")) { mpz_set_ui(x, 1); }
    }
    time_t t0 = time(0);
    while (stp < N) {
        if (trace && stp < trace) { printf("%lld %d ", stp, flag); mpz_out_str(stdout, 10, x); putchar(' '); mpz_out_str(stdout, 10, y); putchar('\n'); }
        int r = step();
        if (r) { printf("%s at map step %lld (state before the step: flag %d, x %ld bits)\n", r == 1 ? "HALT" : "SMALL", stp, flag, (long)mpz_sizeinbase(x, 2));
                 save(ck); FILE *o = fopen("HALT_FOUND", "a"); fprintf(o, "%s %s %lld\n", map, r == 1 ? "halt" : "small", stp); fclose(o); return 1; }
        stp++;
        if (stp % R == 0) { save(ck); printf("%s step %lld x %ld bits y %ld bits flag %d maxgap %ld at %lld (%lds)\n", map, stp, (long)mpz_sizeinbase(x, 2), (long)mpz_sizeinbase(y, 2), flag, minbits, minat, (long)(time(0) - t0)); fflush(stdout); }
    }
    save(ck); printf("%s done %lld steps, no halt; x %ld bits y %ld bits; largest gap bits(number)-bits(halting difference) after step 1000: %ld (at step %lld)\n", map, stp, (long)mpz_sizeinbase(x, 2), (long)mpz_sizeinbase(y, 2), minbits, minat);
    return 0;
}
