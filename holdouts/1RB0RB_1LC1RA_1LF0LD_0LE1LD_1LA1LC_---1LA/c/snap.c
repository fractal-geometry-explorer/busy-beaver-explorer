/* snap: the block lengths of the tape of a machine at chosen times.
 *
 *   snap MACHINE STEP1 STEP2 ...
 *
 * Runs MACHINE from blank tape.  At the first step at or after each STEPi at which the head visits a new cell on
 * the right, prints: the step, the state, the number of visited cells, `min=` the smallest distance from the left
 * end that the head has reached since the last line, and the lengths of the blocks of 1s from left to right
 * (single 0s between them; a run of k > 1 zeros is printed as -k; repeats are folded as (..)^n).
 * Build: gcc -O2 -o snap snap.c
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define CAP (1 << 24)
static unsigned char tape[CAP];
static int w[6][2], d[6][2], s[6][2];
static int runs[CAP / 2];
int main(int c, char **v) {
  if (c < 3) { fprintf(stderr, "usage: snap MACHINE STEP...\n"); return 2; }
  const char *m = v[1];
  for (int q = 0; q < 6; q++) for (int r = 0; r < 2; r++) {
    const char *p = m + 7 * q + 3 * r;
    if (p[0] == '-') { s[q][r] = -1; continue; }
    w[q][r] = p[0] - '0'; d[q][r] = p[1] == 'R' ? 1 : -1; s[q][r] = p[2] - 'A';
  }
  long long pos = CAP / 2, lo = pos, hi = pos, i = 0, mn = pos; int st = 0;
  for (int a = 2; a < c; a++) {
    long long mk = atof(v[a]);
    for (;;) {
      int y = tape[pos];
      if (s[st][y] < 0) { printf("HALT at step %lld\n", i); return 0; }
      tape[pos] = w[st][y]; pos += d[st][y]; st = s[st][y]; i++;
      if (pos < 8 || pos > CAP - 8) { printf("tape overflow at step %lld\n", i); return 3; }
      int nw = pos > hi; if (nw) hi = pos;
      if (pos < lo) lo = pos;
      if (pos < mn) mn = pos;
      if (nw && i >= mk) break;
    }
    int n = 0;
    for (long long p = lo; p <= hi;) {
      long long q = p; while (q <= hi && tape[q] == tape[p]) q++;
      if (tape[p]) runs[n++] = q - p; else if (q - p > 1) runs[n++] = -(q - p);
      p = q;
    }
    printf("%lld %c %lld min=%lld:", i, 'A' + st, hi - lo + 1, mn - lo); mn = pos;
    for (int k = 0; k < n;) {
      int best = 1, bp = 1;
      for (int p = 1; p <= 6; p++) {
        int r = 1; while (k + (r + 1) * p <= n && !memcmp(runs + k, runs + k + r * p, p * sizeof(int))) r++;
        if (r >= 3 && r * p > best * bp) { best = r; bp = p; }
      }
      if (best >= 3) { printf(" ("); for (int j = 0; j < bp; j++) printf(j ? " %d" : "%d", runs[k + j]); printf(")^%d", best); k += best * bp; }
      else { printf(" %d", runs[k]); k++; }
    }
    printf("\n"); fflush(stdout);
  }
  return 0;
}
