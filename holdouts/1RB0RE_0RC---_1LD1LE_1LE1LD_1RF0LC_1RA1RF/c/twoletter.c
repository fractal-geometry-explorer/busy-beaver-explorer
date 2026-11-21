// The tape right of every right turn, read in 2-cell letters.
// usage: twoletter MACHINE STEPS [START_STATE [TURN_STATE]]      e.g. twoletter 1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF 10000000000
// At every turn from right to left made in TURN_STATE (default E: E reads 1, 0LC), check that the tape from the head to
// the last 1 is a word of the letters 11 and 01 starting at the head, and count the length m of the block of 1s under
// the head (the frozen block of lean/Pascal.lean; "at end" when only blank tape follows it).  Prints a summary.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: twoletter MACHINE STEPS [START [TURN]]\n"); return 2; }
  const char *M = argv[1];
  long long N = atoll(argv[2]);
  int s = argc > 3 ? argv[3][0] - 'A' : 0, ts = argc > 4 ? argv[4][0] - 'A' : 4;
  int wr[6][2], mv[6][2], nx[6][2];
  for (int q = 0; q < 6; q++)
    for (int b = 0; b < 2; b++) {
      const char *t = M + q * 7 + b * 3;
      if (t[2] == '-') { nx[q][b] = -1; continue; }
      wr[q][b] = t[0] - '0'; mv[q][b] = t[1] == 'R' ? 1 : -1; nx[q][b] = t[2] - 'A';
    }
  long SZ = 1L << 26;
  unsigned char *tp = calloc(SZ, 1);
  long p = SZ / 2, lo = p, hi = p;
  int dir = 1;
  long long good = 0, bad = 0, other = 0, inner[65] = {0}, atend[65] = {0}, firstbad = -1;
  for (long long i = 0; i < N; i++) {
    int b = tp[p];
    if (nx[s][b] < 0) { printf("HALT after %lld steps\n", i + 1); break; }
    int d = mv[s][b];
    if (d != dir) {
      if (dir == 1) {
        if (s != ts) other++;
        else {
          long H = hi;
          while (H > p && !tp[H]) H--;
          int ok = 1;
          for (long q = p; q + 1 <= H; q += 2)
            if (!tp[q + 1]) { ok = 0; break; }
          if (ok) good++; else { bad++; if (firstbad < 0) firstbad = i; }
          long q = p;
          while (tp[q]) q++;
          int m = q - p < 64 ? q - p : 64;
          if (q > H) atend[m]++; else inner[m]++;
        }
      }
      dir = d;
    }
    tp[p] = wr[s][b]; p += d; s = nx[s][b];
    if (p < lo) lo = p;
    if (p > hi) hi = p;
    if (p < 2 || p > SZ - 3) { printf("tape full after %lld steps\n", i); break; }
  }
  printf("%s, start %c, %lld steps: right turns in %c: %lld in 2-cell letters, %lld not (first at step %lld); %lld right turns in other states\n",
         M, argc > 3 ? argv[3][0] : 'A', N, 'A' + ts, good, bad, firstbad, other);
  printf("block under the head at those turns, m: count with more tape after it / count at the right end\n");
  for (int k = 0; k <= 64; k++)
    if (inner[k] || atend[k]) printf("  m=%s%d: %lld / %lld\n", k == 64 ? ">=" : "", k, inner[k], atend[k]);
  return 0;
}
