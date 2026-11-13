/* Print every P-event of 1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE from blank tape:
   moments where the tape is 0^inf (10)^n A> 0^inf.  Usage: ./pevents STEPS */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
/* states A..F = 0..5; halt = -1 */
static const int W[6][2] = {{1,0},{1,0},{1,1},{1,1},{1,0},{0,0}};
static const int M[6][2] = {{1,-1},{-1,1},{1,-1},{-1,-1},{1,-1},{0,1}};
static const int N[6][2] = {{1,3},{2,0},{0,1},{0,4},{5,2},{-1,4}};
int main(int argc, char **argv) {
  long long steps = argc > 1 ? atoll(argv[1]) : 1000000000LL;
  long size = 1 << 22; unsigned char *t = calloc(size, 1);
  long pos = size / 2, lo = pos, hi = pos; int s = 0;
  for (long long i = 0; i < steps; i++) {
    if (pos <= 1 || pos >= size - 2) { fprintf(stderr, "tape full\n"); return 1; }
    int c = t[pos];
    if (s == 0 && c == 0 && pos + 4 >= hi && !t[pos + 1] && !t[pos + 2] && !t[pos + 3] && !t[pos + 4]) {
      /* candidate: everything right of pos blank; check left part is (10)^n */
      long p = pos - 1, n = 0; int ok = 1;
      while (p >= lo && (t[p] || t[p - 1])) { if (!(t[p] == 0 && t[p - 1] == 1)) { ok = 0; break; } n++; p -= 2; }
      if (ok) { for (long q = lo; q <= p; q++) if (t[q]) { ok = 0; break; } }
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
