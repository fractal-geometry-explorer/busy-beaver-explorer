/* Bare transition table of 1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE from a round start given by marks.
   Input: W n t1 p1 ... (marks beyond the gap at 1; t in G M W B).  Tape as in Lean's roundStart: cell 0 = 1,
   gap 1..3, head on cell 3 in state E, stripes from cell 4 starting with 1, blank from W on.
   Output: halt step and head position relative to W, or "nohalt" after the step limit. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
  long long lim = argc > 1 ? atoll(argv[1]) : 100000000000LL;
  long W; int n; if (scanf("%ld %d", &W, &n) != 2) return 1;
  long N = 4 * W + 1000, off = 2 * W + 500;
  unsigned char *t = calloc(N, 1);
  t[off + 0] = 1;
  long pos = 4; int prev = 0;
  for (int i = 0; i <= n; i++) {
    char ty = 'X'; long p = W;
    if (i < n && scanf(" %c %ld", &ty, &p) != 2) return 1;
    int b = !prev; for (long c = pos; c < p; c++) { t[off + c] = b; b = !b; }
    if (i == n) break;
    int len = (ty == 'G' || ty == 'B') ? 3 : 2, val = (ty == 'M' || ty == 'B');
    for (int k = 0; k < len; k++) t[off + p + k] = val;
    pos = p + len; prev = val;
  }
  /* states A..F = 0..5; table[state][read] = write, move(+1 R / -1 L), next (-1 halt) */
  static const int wr[6][2] = {{1,0},{1,0},{1,1},{1,0},{0,0},{0,1}};
  static const int mv[6][2] = {{1,1},{-1,1},{-1,-1},{-1,0},{1,-1},{-1,1}};
  static const int nx[6][2] = {{1,4},{2,0},{0,3},{0,-1},{5,1},{3,4}};
  long h = off + 3; int s = 4;
  for (long long st = 0; st < lim; st++) {
    int r = t[h];
    if (nx[s][r] < 0) { printf("halt after %lld steps, head at cell %ld (W=%ld)\n", st, h - off, W); return 0; }
    t[h] = wr[s][r]; h += mv[s][r]; s = nx[s][r];
    if (h <= 0 || h >= N - 1) { printf("ran off buffer at step %lld\n", st); return 0; }
  }
  printf("nohalt within %lld steps\n", lim); return 0;
}
