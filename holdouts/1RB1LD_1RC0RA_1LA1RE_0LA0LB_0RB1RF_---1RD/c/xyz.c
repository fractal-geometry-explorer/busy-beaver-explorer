/* xyz.c: the register map of 1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD (lean/Model.lean `nxt`, in the real counts
   of py/orbit.py `single`, with the bulk runs of py/orbit.py `jump`), from X(2,0,3).  Halt: Z(a, 2).
   usage: xyz ROUNDS REPORT CKPT [trace R]  (trace prints N of the first R rounds) */
#include <stdlib.h>
#include <time.h>
#include "../../../tools/c/gmp_decl.h"
static mpz_t a, b, c, k, t;
int main(int argc, char **argv) {
    long long RR = atoll(argv[1]), Rp = atoll(argv[2]); const char *ck = argv[3]; long long trace = argc > 5 ? atoll(argv[5]) : 0;
    mpz_init(a); mpz_init(b); mpz_init(c); mpz_init(k); mpz_init(t);
    int md = 'X'; long long r = 0, js = 0; long gapmax = -1; long long gapat = -1;
    FILE *in = fopen(ck, "r");
    if (in) { if (fscanf(in, "%d %lld %lld %ld %lld", &md, &r, &js, &gapmax, &gapat) != 5) return 4; mpz_inp_str(a, in, 16); mpz_inp_str(b, in, 16); mpz_inp_str(c, in, 16); fclose(in); }
    else { mpz_set_ui(a, 2); mpz_set_ui(b, 0); mpz_set_ui(c, 3); }
    time_t t0 = time(0); long nbits = 0;
    while (r < RR) {
        js++;
        if (md == 'X') {
            if (mpz_cmp_ui(c, 2) >= 0) {
                if (mpz_cmp_ui(a, 4) >= 0) {  /* k = min((a-1)/3, c-1): a -= 3k, b += 2k, c -= k */
                    mpz_sub_ui(k, a, 1); mpz_tdiv_q_ui(k, k, 3); mpz_sub_ui(t, c, 1); if (mpz_cmp(t, k) < 0) mpz_set(k, t);
                    mpz_sub(a, a, k); mpz_sub(a, a, k); mpz_sub(a, a, k); mpz_add(b, b, k); mpz_add(b, b, k); mpz_sub(c, c, k);
                } else if (mpz_cmp_ui(a, 3) == 0) { mpz_set_ui(a, 1); mpz_add_ui(b, b, 1); mpz_sub_ui(c, c, 1); }
                else if (mpz_cmp_ui(a, 2) == 0) { mpz_sub_ui(k, c, 1); mpz_add(b, b, k); mpz_add(b, b, k); mpz_set_ui(c, 1); }
                else if (mpz_cmp_ui(a, 1) == 0) { md = 'Y'; mpz_set_ui(a, 3); mpz_sub_ui(c, c, 1); }
                else if (mpz_sgn(b) == 0) { md = 'Z'; mpz_set_ui(a, 3); mpz_sub_ui(c, c, 1); }
                else { md = 'Y'; mpz_set_ui(a, 3); mpz_sub_ui(b, b, 1); mpz_sub_ui(c, c, 1); }
            } else { /* c == 1 */
                mpz_mul_2exp(t, b, 1);   /* 2b */
                if (mpz_cmp_ui(a, 5) >= 0) { mpz_sub_ui(a, a, 5); mpz_add_ui(c, t, 9); mpz_set_ui(b, 0); }
                else if (mpz_cmp_ui(a, 4) == 0) { mpz_add_ui(c, t, 7); mpz_set_ui(b, 0); }
                else if (mpz_cmp_ui(a, 3) == 0) { mpz_set_ui(a, 4); mpz_add_ui(c, t, 5); mpz_set_ui(b, 0); }
                else if (mpz_cmp_ui(a, 2) == 0) { mpz_set_ui(a, 0); mpz_add_ui(c, t, 9); mpz_set_ui(b, 0); }
                else if (mpz_cmp_ui(a, 1) == 0) { mpz_add_ui(c, t, 5); mpz_set_ui(b, 0); }
                else if (mpz_sgn(b) == 0) { mpz_set_ui(a, 1); mpz_set_ui(c, 3); }
                else { mpz_set_ui(a, 1); mpz_add_ui(c, t, 3); mpz_set_ui(b, 0); }
            }
        } else if (md == 'Y') {
            if (mpz_sgn(b) > 0 && mpz_cmp_ui(c, 2) >= 0) {
                /* a Y run that empties b: halting needs c - b = 3 (record the closest approach) */
                if (mpz_cmp(c, b) > 0 && r >= 3) { mpz_sub(t, c, b); mpz_sub_ui(t, t, 3); long g = (long)nbits - (mpz_sgn(t) ? (long)mpz_sizeinbase(t, 2) : 0); if (g > gapmax) { gapmax = g; gapat = r; } }
                mpz_sub_ui(t, c, 1); if (mpz_cmp(b, t) < 0) mpz_set(k, b); else mpz_set(k, t);
                mpz_add(a, a, k); mpz_add(a, a, k); mpz_add(a, a, k); mpz_sub(b, b, k); mpz_sub(c, c, k);
            } else if (mpz_sgn(b) == 0 && mpz_cmp_ui(c, 2) >= 0) { md = 'Z'; mpz_add_ui(a, a, 3); mpz_sub_ui(c, c, 1); }
            else { md = 'X'; mpz_mul_2exp(t, b, 1); mpz_add_ui(c, t, 3); mpz_set_ui(b, 1); }
        } else { /* Z(a, c) */
            if (mpz_cmp_ui(c, 6) >= 0) { md = 'X'; mpz_add_ui(a, a, 4); mpz_set_ui(b, 0); mpz_sub_ui(c, c, 5); }
            else {
                unsigned long cc = mpz_getlimbn_(c);
                if (cc == 2) { printf("HALT: Z(a, 2) in round %lld\n", r); FILE *o = fopen("HALT_FOUND", "a"); fprintf(o, "xyz halt round %lld\n", r); fclose(o); return 1; }
                md = 'X';
                if (cc == 1) { mpz_set_ui(b, 1); mpz_set_ui(c, 1); }
                else if (cc == 3) { mpz_set_ui(b, 0); mpz_set_ui(c, 5); }
                else if (cc == 4) { mpz_add_ui(a, a, 2); mpz_set_ui(b, 0); mpz_set_ui(c, 3); }
                else if (cc == 5) { mpz_add_ui(a, a, 2); mpz_set_ui(b, 0); mpz_set_ui(c, 5); }
                else { printf("bad Z\n"); return 5; }
            }
        }
        if (md == 'X' && mpz_sgn(a) == 0 && mpz_sgn(b) == 0) {
            r++; nbits = (long)mpz_sizeinbase(c, 2);
            if (trace && r <= trace) { mpz_out_str(stdout, 10, c); putchar('\n'); }
            if (r % Rp == 0) {
                char tmp[4096]; snprintf(tmp, sizeof tmp, "%s.tmp", ck); FILE *o = fopen(tmp, "w");
                fprintf(o, "%d %lld %lld %ld %lld\n", md, r, js, gapmax, gapat); mpz_out_str(o, 16, a); fputc('\n', o); mpz_out_str(o, 16, b); fputc('\n', o); mpz_out_str(o, 16, c); fputc('\n', o); fclose(o); rename(tmp, ck);
                if (!trace) { printf("round %lld: N %ld bits, jump steps %lld, closest Y end: |c-b-3| %ld bits below N (round %lld) (%lds)\n", r, nbits, js, gapmax, gapat, (long)(time(0) - t0)); fflush(stdout); }
            }
        }
    }
    printf("done %lld rounds, no halt: N %ld bits, %lld jump steps; closest approach |c-b-3| had %ld bits fewer than N (round %lld)\n", r, nbits, js, gapmax, gapat);
    return 0;
}
