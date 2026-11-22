/* The watched twin of lean/watch/Machine.lean: the table of 1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF with B0 going
   to a seventh state G (G0 = 1LD as C0, G1 halts).  It halts exactly at a break of lean/Twin.lean (the twin in B with
   a 1 in one of the two cells ahead), so a run without a halt is a run of the twin without a break.
   usage: gcc -O2 -o watch c/watch.c && ./watch 3000000000 */
#include <stdio.h>
#include <stdlib.h>
int main(int argc, char **argv) {
  long long lim = argc > 1 ? atoll(argv[1]) : 1000000000LL;
  /* states A..G = 0..6; {write, move (+1 right, -1 left), next (-1 halts)} */
  int t[7][2][3] = {{{1, 1, 1}, {0, 1, 4}}, {{0, 1, 6}, {0, 0, -1}}, {{1, -1, 3}, {1, -1, 4}}, {{1, -1, 4}, {1, -1, 3}},
                    {{1, 1, 5}, {0, -1, 2}}, {{1, 1, 0}, {1, 1, 5}}, {{1, -1, 3}, {0, 0, -1}}};
  long S = 1L << 22, p = S / 2, lo = p, hi = p;
  unsigned char *tape = calloc(S, 1);
  int s = 0;
  for (long long n = 0; n < lim; n++) {
    int *x = t[s][tape[p]];
    if (x[2] < 0) { printf("halt (a break) at step %lld in state %c\n", n, 'A' + s); return 0; }
    tape[p] = x[0]; p += x[1]; s = x[2];
    if (p < lo) lo = p;
    if (p > hi) hi = p;
    if (p < 1 || p >= S - 1) { printf("out of tape at step %lld\n", n); return 1; }
  }
  printf("no halt (no break) in %lld steps, %ld cells visited\n", lim, hi - lo + 1);
  return 0;
}
