// The odometer of 1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC as a doubling map with a growing modulus.
// For S(c, a, b) put u = b + 1, m = a/2 + b + 2 (so a = 2(m - u - 1)).  One operation:
//   2u < m          u <- 2u,      m <- m + 1                      (the fast wheel doubles; a new visit S)
//   2u > m, c >= 1  u <- 2u - m,  m <- m + 1,  c <- c - 1         (carry)
//   2u = m, c >= 1  u <- 1,       m <- m + 2,  c <- c - 1         (carry that empties the fast wheel)
//   2u > m, c = 0   c <- 2(m - u - 1),  u <- 2u - m,  m <- u + 3  (reset)
//   2u = m, c = 0   halt
// usage: odo MAXOPS [dump N]     (gcc -O2 -o odo odo.c)   "dump N" prints the first N visits "c a b" (for tests)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned long long ull;
int main(int argc, char **argv) {
  ull max = strtoull(argv[1], 0, 10);
  long long dump = argc > 3 && !strcmp(argv[2], "dump") ? atoll(argv[3]) : 0;
  ull c = 0, u = 2, m = 5;                 // S(0, 4, 1), reached at step 43 from blank tape
  ull ops = 0, resets = 0, visits = 0, zeros = 0;
  if (dump) printf("%llu %llu %llu\n", c, 2 * (m - u - 1), u - 1);
  while (ops < max) {
    ull t = 2 * u;
    ops++;
    if (t < m) {
      u = t; m++; visits++;
      if (dump) { if ((long long)visits >= dump) return 0; printf("%llu %llu %llu\n", c, 2 * (m - u - 1), u - 1); }
    } else if (c) {
      c--;
      if (t > m) { u = t - m; m++; } else { u = 1; m += 2; zeros++; }
    } else if (t > m) {
      ull nc = 2 * (m - u - 1);
      resets++;
      if (!dump) printf("reset %llu: op %llu, visit %llu, m = %llu, 2u - m = %llu, new left block c = %llu\n", resets, ops, visits, m, t - m, nc);
      c = nc; u = t - m; m = u + 3;
    } else {
      printf("HALT at operation %llu (after %llu resets): reset with 2u = m = %llu\n", ops, resets, m);
      return 0;
    }
    if (m >> 62) { printf("OVERFLOW\n"); return 2; }
  }
  if (!dump) printf("no halt: %llu operations, %llu visits, %llu resets, %llu emptying carries; now c = %llu, u = %llu, m = %llu\n", ops, visits, resets, zeros, c, u, m);
  return 0;
}
