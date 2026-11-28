/* Every word W of length n (then 0s): run 1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB from `0 0 0 1 1 A> W`
   with the head confined right of the five region cells (stepping left of them is an exit).  Counts halts,
   exits by (state, the six cells from the region start), and runs past LIMIT steps.
   usage: pexh N LIMIT */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static const int W_[6][2] = {{1,0},{0,0},{1,1},{1,1},{0,1},{-1,1}};
static const int D_[6][2] = {{1,-1},{-1,1},{1,-1},{1,-1},{-1,-1},{0,-1}};
static const int S_[6][2] = {{1,4},{2,1},{3,3},{0,5},{1,4},{-1,1}};
int main(int argc, char **argv) {
  int n = atoi(argv[1]); long lim = atol(argv[2]);
  static unsigned char tp[1 << 16];
  long halts = 0, over = 0, ret = 0; long ex[6][64]; memset(ex, 0, sizeof ex);
  for (long w = 0; w < (1L << n); w++) {
    memset(tp, 0, 64 + n + 4096 > sizeof tp ? sizeof tp : 64 + n + 4096);
    tp[3] = 1; tp[4] = 1;
    for (int i = 0; i < n; i++) tp[5 + i] = (w >> i) & 1;
    int pos = 5, st = 0; long t;
    for (t = 0; t < lim; t++) {
      if (pos < 0) break;
      if (pos >= (int)sizeof tp - 2) { t = lim; break; }
      int b = tp[pos];
      if (W_[st][b] < 0) { halts++; fprintf(stderr, "HALT w=%lx n=%d\n", w, n); break; }
      tp[pos] = W_[st][b]; int s2 = S_[st][b]; pos += D_[st][b]; st = s2;
    }
    if (t >= lim) over++;
    else if (pos < 0) { int k = 0; for (int i = 0; i < 6; i++) k |= tp[i] << i; ex[st][k]++; }
  }
  printf("n=%d halts=%ld over=%ld\n", n, halts, over);
  for (int s = 0; s < 6; s++) for (int k = 0; k < 64; k++) if (ex[s][k]) {
    printf("exit %c ", "ABCDEF"[s]); for (int i = 0; i < 6; i++) putchar('0' + ((k >> i) & 1)); printf(" %ld\n", ex[s][k]); }
  return 0;
}
