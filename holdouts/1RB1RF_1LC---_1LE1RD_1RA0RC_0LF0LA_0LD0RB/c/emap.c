/* emap.c: emap of lean/Map.lean (1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB) from D(3, 0), with runs of drain steps
   (n even, k >= 2) done at once as in py/emap.py `jump`.  Halt: n odd and k = 1.
   usage: emap EPOCHS REPORT_EPOCHS CKPT [trace N]   (trace prints the first N epoch values N) */
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "../../../tools/c/gmp_decl.h"
int main(int argc, char **argv) {
    long long E = atoll(argv[1]), Rp = atoll(argv[2]); const char *ck = argv[3]; long long trace = argc > 5 ? atoll(argv[5]) : 0;
    mpz_t n, k, t; mpz_init(n); mpz_init(k); mpz_init(t);
    int s = 1; /* 0 = A, 1 = D */ long long ep = 0, jsteps = 0; mpz_t lsteps; mpz_init(lsteps); /* Lean emap steps */
    FILE *in = fopen(ck, "r");
    if (in) { if (fscanf(in, "%d %lld %lld", &s, &ep, &jsteps) != 3) return 4; mpz_inp_str(n, in, 16); mpz_inp_str(k, in, 16); mpz_inp_str(lsteps, in, 16); fclose(in); }
    else { mpz_set_ui(n, 3); mpz_set_ui(k, 0); }
    time_t t0 = time(0);
    while (ep < E) {
        jsteps++;
        int kz = mpz_sgn(k) == 0, ne = !mpz_odd_p(n);
        if (kz) {
            mpz_add_ui(lsteps, lsteps, 1);
            if (ne) { mpz_add_ui(n, n, 3); s = !s; }
            else { mpz_add_ui(k, n, 1); mpz_fdiv_q_2exp_(k, k); mpz_set_ui(n, s == 0 ? 1 : 3); s = 1; }
        } else if (ne) {
            if (mpz_cmp_ui(k, 1) == 0) { mpz_add_ui(lsteps, lsteps, 1); mpz_add_ui(n, n, 7); mpz_set_ui(k, 0); s = !s; }
            else { /* j = k - 1 drain steps: n += 4j, k = 1, state flips j times */
                mpz_sub_ui(t, k, 1); mpz_add(lsteps, lsteps, t);
                if (mpz_odd_p(t)) s = !s;
                mpz_mul_ui(t, t, 4); mpz_add(n, n, t); mpz_set_ui(k, 1);
            }
        } else {
            if (mpz_cmp_ui(k, 1) == 0) {
                printf("HALT: state %c(n, 1) with n odd (n %ld bits) after %lld jump steps, %lld epochs\n", s ? 'D' : 'A', (long)mpz_sizeinbase(n, 2), jsteps, ep);
                FILE *o = fopen("HALT_FOUND", "a"); fprintf(o, "emap halt epoch %lld\n", ep); fclose(o); return 1;
            }
            mpz_add_ui(lsteps, lsteps, 1);
            /* compare 2k with n + 5 */
            mpz_mul_2exp(t, k, 1); mpz_sub(t, t, n); mpz_sub_ui(t, t, 5);   /* t = 2k - n - 5 */
            int c = s ? 7 : 6;
            if (mpz_sgn(t) > 0) { /* (s, 2n + c, k - (n+5)/2) */
                mpz_add_ui(t, n, 5); mpz_fdiv_q_2exp_(t, t); mpz_sub(k, k, t); mpz_mul_2exp(n, n, 1); mpz_add_ui(n, n, c);
            } else if (mpz_sgn(t) == 0) { mpz_mul_2exp(n, n, 1); mpz_add_ui(n, n, c + 3); mpz_set_ui(k, 0); }
            else { /* (oth, n + 6 - 2k, 2k) */
                mpz_mul_2exp(k, k, 1); mpz_sub(n, n, k); mpz_add_ui(n, n, 6); s = !s;
            }
        }
        if (mpz_sgn(k) == 0 && s == 1) {
            ep++;
            if (trace && ep <= trace) { mpz_out_str(stdout, 10, n); putchar(' '); }
            if (ep % Rp == 0) {
                char tmp[4096]; snprintf(tmp, sizeof tmp, "%s.tmp", ck); FILE *o = fopen(tmp, "w");
                fprintf(o, "%d %lld %lld\n", s, ep, jsteps); mpz_out_str(o, 16, n); fputc('\n', o); mpz_out_str(o, 16, k); fputc('\n', o); mpz_out_str(o, 16, lsteps); fputc('\n', o); fclose(o); rename(tmp, ck);
                if (!trace) { printf("epoch %lld: N %ld bits, jump steps %lld, emap steps %ld bits (%lds)\n", ep, (long)mpz_sizeinbase(n, 2), jsteps, (long)mpz_sizeinbase(lsteps, 2), (long)(time(0) - t0)); fflush(stdout); }
            }
        }
    }
    if (trace) putchar('\n');
    printf("done %lld epochs, no halt: N %ld bits, %lld jump steps, emap steps ~2^%ld\n", ep, (long)mpz_sizeinbase(n, 2), jsteps, (long)mpz_sizeinbase(lsteps, 2));
    return 0;
}
