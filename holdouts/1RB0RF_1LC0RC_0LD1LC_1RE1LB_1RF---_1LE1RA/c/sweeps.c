// sweeps STEPS [MINBLOCK]: run 1RB0RF_1LC0RC_0LD1LC_1RE1LB_1RF---_1LE1RA from blank tape and, each time the head
// reaches one end of the visited region after having been at the other (a full sweep), print
// "step side state width tape" with the tape run-length coded over the tokens a = 10 and 1 (first 60 tokens).
// With MINBLOCK > 0 only sweeps whose tape holds a block of at least MINBLOCK ones are printed.
// usage: gcc -O2 -o sweeps sweeps.c && ./sweeps 3000000000 1000
#include <stdio.h>
#include <stdlib.h>
#define N (1 << 24)
static unsigned char t[N];
static void show(long long i, char side, char st, long lo, long hi, long minb) {
  long best = 0, run = 0;
  for (long q = lo; q <= hi; q++) { run = t[q] ? run + 1 : 0; if (run > best) best = run; }
  if (best < minb) return;
  printf("%lld %c %c %ld", i, side, st, hi - lo + 1);
  int tokens = 0; long q = lo; char prev = 0; long cnt = 0;
  while (q <= hi && tokens < 60) {
    char c; if (t[q] == 1 && q + 1 <= hi && t[q + 1] == 0) { c = 'a'; q += 2; } else if (t[q] == 1) { c = '1'; q++; } else { c = '0'; q++; }
    if (c == prev) { cnt++; continue; }
    if (prev) { if (cnt > 1) printf(" %c^%ld", prev, cnt); else printf(" %c", prev); tokens++; }
    prev = c; cnt = 1;
  }
  if (prev) { if (cnt > 1) printf(" %c^%ld", prev, cnt); else printf(" %c", prev); }
  printf("%s  [longest block of ones: %ld]\n", q <= hi ? " ..." : "", best);
  fflush(stdout);
}
int main(int argc, char **argv) {
  const char *m = "1RB0RF_1LC0RC_0LD1LC_1RE1LB_1RF---_1LE1RA";
  long long steps = argc > 1 ? atoll(argv[1]) : 1000000000LL; long minb = argc > 2 ? atol(argv[2]) : 0;
  int nw[6][2], mv[6][2], ns[6][2];
  for (int s = 0; s < 6; s++) for (int r = 0; r < 2; r++) {
    const char *x = m + s * 7 + r * 3;
    if (x[0] == '-') { ns[s][r] = -1; continue; }
    nw[s][r] = x[0] - '0'; mv[s][r] = x[1] == 'R' ? 1 : -1; ns[s][r] = x[2] - 'A';
  }
  long p = N / 2, lo = p, hi = p; int s = 0, last = 0;
  for (long long i = 0; i < steps; i++) {
    int r = t[p], n = ns[s][r];
    if (n < 0) { printf("HALT %lld\n", i); return 0; }
    t[p] = nw[s][r]; p += mv[s][r]; s = n;
    if (p < lo) lo = p;
    if (p > hi) hi = p;
    if (p < 2 || p > N - 2) { printf("OUT %lld\n", i); return 0; }
    int side = p == lo ? -1 : p == hi ? 1 : 0;
    if (side && side != last) {
      last = side;
      if (minb == 0 || side == 1) show(i + 1, side < 0 ? 'L' : 'R', 'A' + s, lo, hi, minb);
    }
  }
  printf("END %lld\n", steps);
  return 0;
}
