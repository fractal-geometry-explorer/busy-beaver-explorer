/* Exits of the trip of 1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB from `0 0 0 1 1 A> W`, by the first P cells of
   W: for every word W of n cells (then 0s), prints once each "prefix state cells" with the L cells from the
   region start at the exit (cell 0 = first region cell), and reports halts and runs past LIMIT.
   usage: pexp N P L LIMIT */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static const int W_[6][2] = {{1,0},{0,0},{1,1},{1,1},{0,1},{-1,1}};
static const int D_[6][2] = {{1,-1},{-1,1},{1,-1},{1,-1},{-1,-1},{0,-1}};
static const int S_[6][2] = {{1,4},{2,1},{3,3},{0,5},{1,4},{-1,1}};
int main(int argc, char **argv) {
  int n = atoi(argv[1]), P = atoi(argv[2]), L = atoi(argv[3]); long lim = atol(argv[4]);
  static unsigned char tp[1 << 16];
  unsigned char *seen = calloc((size_t)6 << (P + L), 1);
  long halts = 0, over = 0;
  for (long w = 0; w < (1L << n); w++) {
    memset(tp, 0, 4096);
    tp[3] = 1; tp[4] = 1;
    for (int i = 0; i < n; i++) tp[5 + i] = (w >> i) & 1;
    int pos = 5, st = 0; long t;
    for (t = 0; t < lim; t++) {
      if (pos < 0) break;
      if (pos >= 4000) { t = lim; break; }
      int b = tp[pos];
      if (W_[st][b] < 0) { halts++; break; }
      tp[pos] = W_[st][b]; int s2 = S_[st][b]; pos += D_[st][b]; st = s2;
    }
    if (t >= lim) { over++; continue; }
    if (pos >= 0) continue;
    long k = 0; for (int i = 0; i < L; i++) k |= (long)tp[i] << i;
    long p = w & ((1L << P) - 1);
    size_t idx = (((size_t)st << P) | p) << L | k;
    if (!seen[idx]) {
      seen[idx] = 1;
      for (int i = 0; i < P; i++) putchar('0' + ((p >> i) & 1));
      printf(" %c ", "ABCDEF"[st]);
      for (int i = 0; i < L; i++) putchar('0' + ((k >> i) & 1));
      putchar('\n');
    }
  }
  fprintf(stderr, "n=%d halts=%ld over=%ld\n", n, halts, over);
  return 0;
}
