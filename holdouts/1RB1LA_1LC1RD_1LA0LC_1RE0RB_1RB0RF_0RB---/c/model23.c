/* Round map of the closed counter model coq/SOC23Model.v (same as py/model23.py), with GMP.
   1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB--- and 1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_1RC---.

   A round goes from cfgL L 0 X to the next cfgL L' 0 X'. It is computed in "deficit" form:
   D = 2^len - 1 - k is how far the left counter is below full. The left counter starts full (D = 0);
   a countdown of n subtracts n (D += n), and an overflow that appends s digits sends D to (2D+1)*2^s.
   The round ends either with X fully read (rules R1b, R2b, R3b) or with rule R5, leaving the unread part m:
     X' = 2^L' - (2D+1)*2^s + m + 1      (R5)
     X' = 2^L' - (2D+1)*2^s + 1          (R1b)      X' = 2^L' - (2D+1)*2^s   (R2b, R3b)
   so X' = 2^L' (a corner, the only way to halt) exactly when m + 1 = (2D+1)*2^s at an R5 end.

   usage: model23 ROUNDS [EVERY]     prints a line every EVERY rounds (default 1000), with
          the smallest value of bits(|X - 2^L|) / L seen after round 4, and the largest share of X
          (bits read / L) that one round reads after the last round that read all of X (round 9), and
          from round 35 on.
          A corner needs one round to read a large share of X: m + 1 = (2D+1)*2^s has at most about
          L' - L + 1 bits, so the unread part m must be that short.
   build: gcc -O2 -o model23 model23.c -lgmp */
#include <gmp.h>
#include <stdio.h>
#include <stdlib.h>

static mpz_t X, m, D, T, tmp;
static unsigned long L;
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
    a = h / 2; (*steps)++;
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
  long N = argc > 1 ? atol(argv[1]) : 2000, EVERY = argc > 2 ? atol(argv[2]) : 1000;
  mpz_inits(X, m, D, T, tmp, NULL);
  L = 2; mpz_set_ui(X, 5);
  double closest = 1e9, maxread = 0, maxread35 = 0; long closest_t = -1, maxread_t = -1, maxread35_t = -1, nreb = 0;
  for (long t = 0; t < N; t++) {
    unsigned long L0 = L;
    int steps; int e = round_map(&steps);
    if (e != 5) nreb++;
    else if (t >= 9) {   /* the share of X that an R5 round reads, after round 9 (the last round that read all of X) */
      double rd = (double)(xbits - mbits) / L0;
      if (rd > maxread) { maxread = rd; maxread_t = t; }
      if (t >= 34 && rd > maxread35) { maxread35 = rd; maxread35_t = t; }
    }
    /* distance to the corner */
    mpz_set_ui(tmp, 0); mpz_setbit(tmp, L); mpz_sub(tmp, X, tmp);
    if (mpz_sgn(tmp) == 0) { printf("CORNER after round %ld, L = %lu\n", t, L); return 0; }
    double r = (double)mpz_sizeinbase(tmp, 2) / L;
    if (t > 3 && r < closest) { closest = r; closest_t = t; }
    if ((t + 1) % EVERY == 0 || t == N - 1 || t < 3) {
      printf("round %ld: L = %lu, X - 2^L %s, %zu bits; rebuild rounds so far %ld; smallest bits/L since round 4: %.4f (round %ld); "
             "largest share of X read by one round since round 10: %.3f (round %ld), since round 35: %.3f (round %ld); low64 %lx\n",
             t + 1, L, mpz_sgn(tmp) > 0 ? "> 0" : "< 0", mpz_sizeinbase(tmp, 2), nreb, closest, closest_t + 1,
             maxread, maxread_t + 1, maxread35, maxread35_t + 1, (unsigned long)mpz_getlimbn(X, 0));
      fflush(stdout);
    }
  }
  return 0;
}
