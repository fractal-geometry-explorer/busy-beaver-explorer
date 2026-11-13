/* front MACHINE MAXSTEPS
 *
 * How far behind the right end of the tape does the head go?  Plain simulation from blank tape; at steps 10^6 * 2^k
 * one line for the interval since the previous line:
 *   t      the step count
 *   lo hi  the leftmost and rightmost visited cells (relative to the start cell)
 *   min    the leftmost cell the head was on during the interval
 *   depth  the largest distance between the head and the rightmost visited cell during the interval
 *   recs   the number of new rightmost cells in the interval
 * "HALT STEP" if the machine halts.  3.3*10^10 steps take about two minutes.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#define N (1L << 27)
static uint8_t *tape;
int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: front MACHINE MAXSTEPS\n"); return 2; }
  const char *m = argv[1];
  unsigned long long maxs = strtoull(argv[2], 0, 10), thr = 1000000, t = 0;
  int W[6][2], D[6][2], S[6][2];
  for (int s = 0; s < 6; s++)
    for (int b = 0; b < 2; b++) {
      const char *p = m + s * 7 + b * 3;
      if (p[0] == '-') { W[s][b] = 1; D[s][b] = 1; S[s][b] = 6; }
      else { W[s][b] = p[0] - '0'; D[s][b] = p[1] == 'R' ? 1 : -1; S[s][b] = p[2] - 'A'; }
    }
  tape = calloc(N, 1);
  long pos = N / 4, lo = pos, hi = pos, minp = pos, depth = 0, recs = 0;
  int st = 0;
  while (t < maxs) {
    int b = tape[pos], ns = S[st][b];
    if (ns == 6) { printf("HALT %llu\n", t + 1); return 0; }
    tape[pos] = W[st][b]; pos += D[st][b]; st = ns; t++;
    if (pos < minp) minp = pos;
    if (hi - pos > depth) depth = hi - pos;
    if (pos > hi) { hi = pos; recs++; }
    if (pos < lo) lo = pos;
    if (t >= thr) {
      printf("t=%llu lo=%ld hi=%ld min=%ld depth=%ld recs=%ld\n", t, lo - N / 4, hi - N / 4, minp - N / 4, depth, recs);
      fflush(stdout);
      thr *= 2; minp = pos; depth = 0; recs = 0;
    }
    if (pos < 8 || pos > N - 8) { fprintf(stderr, "tape full\n"); return 1; }
  }
  return 0;
}
