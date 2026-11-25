/* Per-round data of the round map of coq/SOC23Model.v, for the tail of "how much of X does one round read".
   1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB--- and 1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_1RC---.
   Same round as c/model23.c (deficit form). For every round it prints one line
       t L xbits r tbits mbits end steps hmax zt zm
   L = digits of the left counter at the start, xbits = bits of X, r = bits read (xbits - bits of the unread rest m),
   tbits = bits of the target (2D+1)*2^s at an R5 end, mbits = bits of m+1 (0 for the blank ends R1-R3),
   steps = overflow rules in the cascade, hmax = the longest run it read in one step,
   zt, zm = the zeros right below the leading 1 of the target and of m+1 (a match needs zt = zm).
   By halts_iff_r5_match (coq/SOC23Match.v) a halt needs an R5 round with m+1 = (2D+1)*2^s, so tbits = mbits.
   usage: r5tail ROUNDS > out.txt      build: gcc -O2 -o r5tail r5tail.c -lgmp */
#include <gmp.h>
#include <stdio.h>
#include <stdlib.h>

static mpz_t X, m, D, T, tmp;
static unsigned long L;
static unsigned long hmax;      /* longest run 0^h 1 (or 1^h 0) read in the round */
static size_t xbits, mbits;   /* bits of X at the start of the round, of the unread part m at an R5 end */

/* m = (x*2+1)*2^i: returns i and sets m to x */
static unsigned long split(mpz_t v) {
  unsigned long i = mpz_scan1(v, 0);
  mpz_tdiv_q_2exp(v, v, i + 1);
  return i;
}

/* one round; returns end rule: 1 = R1b, 2 = R2b, 3 = R3b, 5 = R5; *steps = overflow rules used */
static int round_map(int *steps) {
  int S1 = 0; unsigned long ln = L, h, a, s;
  mpz_set(m, X);
  xbits = mpz_sizeinbase(X, 2);
  h = split(m);
  mpz_set_ui(D, 0);
  /* n = 2*(2^h-1) for S0 from LC_Ov */
  int nodd = 0;
  *steps = 0;
  for (;;) {
    /* D += n, n = 2*(2^h - 1) + nodd */
    mpz_set_ui(tmp, 0); mpz_setbit(tmp, h + 1); mpz_sub_ui(tmp, tmp, 2 - nodd);
    mpz_add(D, D, tmp);
    a = h / 2; (*steps)++; if (h > hmax) hmax = h;
    int end = 0;
    if (!S1) {
      if (h % 2 == 0) { s = 3 * a;
        if (mpz_sgn(m) == 0) end = 1; else { h = split(m); S1 = 1; nodd = 0; }
      } else { s = 3 * a + 2;
        if (mpz_sgn(m) == 0) end = 2; else { h = split(m); S1 = 0; nodd = 1; }
      }
    } else {
      if (h % 2 == 0) {
        if (mpz_sgn(m) == 0) { s = 3 * a + 2; end = 3; }
        else if (mpz_even_p(m)) { s = 3 * a + 2; mpz_tdiv_q_2exp(m, m, 1); h = split(m); S1 = 1; nodd = 1; }
        else { s = 3 * a + 1; mpz_add_ui(m, m, 1); h = split(m); S1 = 0; nodd = 0; }
      } else { s = 3 * a + 3; end = 5; }
    }
    ln += 1 + s;
    if (end) {
      /* T = (2D+1)*2^s */
      mpz_mul_2exp(T, D, 1); mpz_add_ui(T, T, 1); mpz_mul_2exp(T, T, s);
      L = ln;
      mpz_set_ui(X, 0); mpz_setbit(X, L); mpz_sub(X, X, T);
      if (end == 1) mpz_add_ui(X, X, 1);
      if (end == 5) { mbits = mpz_sgn(m) ? mpz_sizeinbase(m, 2) : 0; mpz_add(X, X, m); mpz_add_ui(X, X, 1); }
      return end;
    }
    mpz_mul_2exp(D, D, 1); mpz_add_ui(D, D, 1); mpz_mul_2exp(D, D, s);
  }
}

int main(int argc, char **argv) {
  long N = argc > 1 ? atol(argv[1]) : 2000;
  mpz_inits(X, m, D, T, tmp, NULL);
  L = 2; mpz_set_ui(X, 5);
  for (long t = 0; t < N; t++) {
    unsigned long L0 = L;
    int steps; hmax = 0; int e = round_map(&steps);
    size_t tb = 0, mb = 0;
    long zt = -1, zm = -1;   /* zeros right below the leading 1 of T and of m+1 (-1: no other 1) */
    if (e == 5) {
      tb = mpz_sizeinbase(T, 2); mpz_add_ui(tmp, m, 1); mb = mpz_sizeinbase(tmp, 2);
      mpz_clrbit(tmp, mb - 1); if (mpz_sgn(tmp)) zm = (long)(mb - 1 - mpz_sizeinbase(tmp, 2));
      mpz_set(tmp, T); mpz_clrbit(tmp, tb - 1); if (mpz_sgn(tmp)) zt = (long)(tb - 1 - mpz_sizeinbase(tmp, 2));
    }
    printf("%ld %lu %zu %zu %zu %zu %d %d %lu %ld %ld\n", t, L0, xbits, e == 5 ? xbits - mbits : xbits, tb, mb, e, steps, hmax, zt, zm);
    mpz_set_ui(tmp, 0); mpz_setbit(tmp, L);
    if (mpz_cmp(tmp, X) == 0) { printf("CORNER after round %ld\n", t); return 0; }
    if (t % 1000 == 0) fflush(stdout);
  }
  return 0;
}
