/* Print every P-event of 1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB from blank tape:
   moments where the tape is 0^inf E> 0 0 1^n 0 1 0^inf.  Usage: ./pevents STEPS */
#include <stdio.h>
#include <stdlib.h>
/* states A..F = 0..5; halt = -1.  1RB0LE 1LB1RC 0RF0RD 1RE0LA 1LA1RE ---0RB */
static const int W[6][2] = {{1,0},{1,1},{0,0},{1,0},{1,1},{0,0}};
static const int M[6][2] = {{1,-1},{-1,1},{1,1},{1,-1},{-1,1},{0,1}};
static const int N[6][2] = {{1,4},{1,2},{5,3},{4,0},{0,4},{-1,1}};
int main(int argc, char **argv) {
  long long steps = argc > 1 ? atoll(argv[1]) : 1000000000LL;
  long size = 1 << 22; unsigned char *t = calloc(size, 1);
  long pos = size / 2, lo = pos, hi = pos; int s = 0;
  for (long long i = 0; i < steps; i++) {
    if (pos <= 4 || pos >= size - 2) { fprintf(stderr, "tape full\n"); return 1; }
    int c = t[pos];
    if (s == 4 && c == 0 && pos - 4 <= lo && !t[pos - 1] && !t[pos - 2] && !t[pos - 3] && !t[pos - 4]
        && !t[pos + 1] && t[pos + 2]) {
      long p = pos + 2, n = 0;
      while (p <= hi && t[p]) { n++; p++; }
      int ok = p + 1 <= hi && t[p] == 0 && t[p + 1] == 1;
      for (long q = p + 2; ok && q <= hi; q++) if (t[q]) ok = 0;
      if (ok) printf("%lld %ld\n", i, n);
    }
    int ns = N[s][c];
    if (ns < 0) { printf("HALT %lld\n", i + 1); return 0; }
    t[pos] = W[s][c]; pos += M[s][c]; s = ns;
    if (pos < lo) lo = pos; if (pos > hi) hi = pos;
  }
  printf("no halt in %lld steps\n", steps);
  return 0;
}
