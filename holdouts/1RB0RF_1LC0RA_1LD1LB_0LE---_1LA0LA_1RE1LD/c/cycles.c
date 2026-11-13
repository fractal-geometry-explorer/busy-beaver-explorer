// cycles STEPS: run 1RB0RF_1LC0RA_1LD1LB_0LE---_1LA0LA_1RE1LD from blank tape and print the ends of cycles:
//   "A step m"  when the tape is 0^inf A> 1 1 (01)^m 0^inf   (proved in Lean: reaches C> 1^(2m+6))
//   "C step n"  when the tape is 0^inf C> 1^n 0^inf          (proved in Lean: reaches D> (01)^(n+1) 1)
// The check of these patterns is done only when the head is at the left end of the visited region.
// usage: gcc -O2 -o cycles cycles.c && ./cycles 1000000000
#include <stdio.h>
#include <stdlib.h>
#define N (1 << 26)
static unsigned char t[N];
int main(int argc, char **argv) {
  const char *m = "1RB0RF_1LC0RA_1LD1LB_0LE---_1LA0LA_1RE1LD";
  long long steps = argc > 1 ? atoll(argv[1]) : 1000000000LL;
  int nw[6][2], mv[6][2], ns[6][2];
  for (int s = 0; s < 6; s++) for (int r = 0; r < 2; r++) {
    const char *x = m + s * 7 + r * 3;
    if (x[0] == '-') { ns[s][r] = -1; continue; }
    nw[s][r] = x[0] - '0'; mv[s][r] = x[1] == 'R' ? 1 : -1; ns[s][r] = x[2] - 'A';
  }
  long p = N / 2, lo = p, hi = p; int s = 0;
  for (long long i = 0; i < steps; i++) {
    if (p == lo && (s == 0 || s == 2)) {
      long q = p; int ok = 1;
      if (s == 2) { while (q <= hi && t[q]) q++; ok = q > hi; if (ok) printf("C %lld %ld\n", i, hi - p + 1); }
      else if (t[p] && t[p + 1]) {
        q = p + 2; while (q + 1 <= hi && !t[q] && t[q + 1]) q += 2;
        for (long k = q; k <= hi; k++) if (t[k]) ok = 0;
        if (ok) printf("A %lld %ld\n", i, (q - p - 2) / 2);
      }
      fflush(stdout);
    }
    int r = t[p], n = ns[s][r];
    if (n < 0) { printf("HALT %lld\n", i); return 0; }
    t[p] = nw[s][r]; p += mv[s][r]; s = n;
    if (p < lo) lo = p; if (p > hi) hi = p;
    if (p < 2 || p > N - 2) { printf("OUT %lld\n", i); return 0; }
  }
  return 0;
}
