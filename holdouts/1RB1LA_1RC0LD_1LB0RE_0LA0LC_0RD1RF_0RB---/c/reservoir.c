// reservoir STEPS: run 1RB1LA_1RC0LD_1LB0RE_0LA0LC_0RD1RF_0RB--- from blank tape. Each time the head comes to the
// right end of the visited region (after having been at the left end) the tape ends in `(110)^R 1 1 >1`; R is the
// reservoir (-1 if the tape does not end that way). Print "refill step R width" whenever R jumps up, "sample ..."
// at the 2^k-th arrival, and the final state.
// usage: gcc -O2 -o reservoir reservoir.c && ./reservoir 10000000000
#include <stdio.h>
#include <stdlib.h>
#define N (1 << 27)
static unsigned char t[N];
int main(int argc, char **argv) {
  const char *m = "1RB1LA_1RC0LD_1LB0RE_0LA0LC_0RD1RF_0RB---";
  long long steps = argc > 1 ? atoll(argv[1]) : 1000000000LL;
  int nw[6][2], mv[6][2], ns[6][2];
  for (int s = 0; s < 6; s++) for (int r = 0; r < 2; r++) {
    const char *x = m + s * 7 + r * 3;
    if (x[0] == '-') { ns[s][r] = -1; continue; }
    nw[s][r] = x[0] - '0'; mv[s][r] = x[1] == 'R' ? 1 : -1; ns[s][r] = x[2] - 'A';
  }
  long p = N / 2, lo = p, hi = p; int s = 0, last = 0; long prevR = -1; long long arr = 0;
  for (long long i = 0; i < steps; i++) {
    int r = t[p], n = ns[s][r];
    if (n < 0) { printf("HALT %lld\n", i); return 0; }
    t[p] = nw[s][r]; p += mv[s][r]; s = n;
    if (p < lo) lo = p;
    if (p > hi) hi = p;
    if (p < 2 || p > N - 2) { printf("OUT %lld\n", i); return 0; }
    if (p == lo && last != -1) last = -1;
    else if (p == hi && last != 1) {
      last = 1;
      long q = p - 1; long R = -1;
      if (t[q] && t[q - 1]) { q -= 2; R = 0; while (q - 2 >= lo && t[q] == 0 && t[q - 1] && t[q - 2]) { R++; q -= 3; } }
      arr++;
      if (R > prevR + 2 || (arr & (arr - 1)) == 0) { printf("%s %lld %ld %ld\n", R > prevR + 2 ? "refill" : "sample", i + 1, R, hi - lo + 1); fflush(stdout); }
      if (R >= 0) prevR = R;
    }
  }
  printf("END %lld width %ld\n", steps, hi - lo + 1);
  return 0;
}
