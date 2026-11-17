// The odometer of 1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC as a doubling map with a growing modulus.
// For S(c, a, b) put u = b + 1, v = a/2 + b + 2 (so a = 2(v - u - 1)).  One operation:
//   2u < v          u <- 2u,      v <- v + 1                      (the fast wheel doubles; a new visit S)
//   2u > v, c >= 1  u <- 2u - v,  v <- v + 1,  c <- c - 1         (carry)
//   2u = v, c >= 1  u <- 1,       v <- v + 2,  c <- c - 1         (carry that empties the fast wheel)
//   2u > v, c = 0   c <- 2(v - u - 1),  u <- 2u - v,  v <- u + 3  (reset)
//   2u = v, c = 0   halt
// usage: odo MAXOPS [dump N]     (gcc -O2 -o odo odo.c)   "dump N" prints the first N visits "c a b" (for tests)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned long long ull;
int main(int argc, char **argv) {
  ull max = strtoull(argv[1], 0, 10);
  long long dump = argc > 3 && !strcmp(argv[2], "dump") ? atoll(argv[3]) : 0;
  ull c = 0, u = 2, v = 5;                 // S(0, 4, 1), reached at step 43 from blank tape
  ull ops = 0, resets = 0, visits = 0, zeros = 0;
  if (dump) printf("%llu %llu %llu\n", c, 2 * (v - u - 1), u - 1);
  while (ops < max) {
    ull t = 2 * u;
    ops++;
    if (t < v) {
      u = t; v++; visits++;
      if (dump) { if ((long long)visits >= dump) return 0; printf("%llu %llu %llu\n", c, 2 * (v - u - 1), u - 1); }
    } else if (c) {
      c--;
      if (t > v) { u = t - v; v++; } else { u = 1; v += 2; zeros++; }
    } else if (t > v) {
      ull nc = 2 * (v - u - 1);
      resets++;
      if (!dump) printf("reset %llu: op %llu, visit %llu, v = %llu, 2u - v = %llu, new left block c = %llu\n", resets, ops, visits, v, t - v, nc);
      c = nc; u = t - v; v = u + 3;
    } else {
      printf("HALT at operation %llu (after %llu resets): reset with 2u = v = %llu\n", ops, resets, v);
      return 0;
    }
    if (v >> 62) { printf("OVERFLOW\n"); return 2; }
  }
  if (!dump) printf("no halt: %llu operations, %llu visits, %llu resets, %llu emptying carries; now c = %llu, u = %llu, v = %llu\n", ops, visits, resets, zeros, c, u, v);
  return 0;
}
