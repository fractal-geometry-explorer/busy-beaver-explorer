/* smallblock: the family 1RB1RC_1LC0RE_1LD0LB_1RA1LC_????_???? with the block kept short, from random regions.
 *
 * Start: 0^inf D>0 1^BLOCK R, R = L random pairs 01 / 11 (the first is 01), then a single 1 if LONE; with TAIL=cells in
 * the environment the last cells of R are those instead.  The real machine runs from there, except that at every
 * visit (the head extends the tape to the left in state D) the block is cut back to BLOCK or BLOCK + 1 cells (an even
 * number of 1s is removed, which the sweep does not notice).  An *event* is the head reaching the left end in state C
 * and extending the tape in state B: the whole tape becomes the new region.  With short blocks the events follow each
 * other quickly, so a run shows many of them.
 *
 *   smallblock MACHINE L TRIALS SEED LONE MAXEV [BLOCK]
 * runs each trial until a halt or until MAXEV events have happened (0 = no limit), and prints how many trials halted
 * after 0, 1, 2, ... events, and for the halts where the head was: the number of non-blank cells right of it.
 * Build: gcc -O2 -o smallblock smallblock.c
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define CAP (1 << 16)
static int W[6][2], D[6][2], S[6][2];
int main(int c, char **v) {
  if (c < 7) { fprintf(stderr, "usage: smallblock MACHINE L TRIALS SEED LONE MAXEV [BLOCK]\n"); return 1; }
  const char *m = v[1];
  for (int i = 0; i < 6; i++) for (int b = 0; b < 2; b++) { const char *t = m + 7 * i + 3 * b;
    if (t[0] == '-') S[i][b] = -1; else { W[i][b] = t[0] - '0'; D[i][b] = t[1] == 'R' ? 1 : -1; S[i][b] = t[2] - 'A'; } }
  int L = atoi(v[2]); long T = atol(v[3]); srand(atoi(v[4])); int lone = atoi(v[5]), MAXEV = atoi(v[6]), BL = c > 7 ? atoi(v[7]) : 4;
  static unsigned char tp[CAP]; static long hist[4096], right[64]; long lim = 0, full = 0, capped = 0; const char *tl = getenv("TAIL");
  for (long t = 0; t < T; t++) {
    memset(tp, 0, CAP); int base = CAP / 2, q = base + 1; for (int i = 0; i < BL; i++) tp[q++] = 1;
    for (int i = 0; i < L; i++) { tp[q++] = i == 0 ? 0 : (rand() >> 8) & 1; tp[q++] = 1; }
    if (lone) tp[q++] = 1;
    if (tl) { int n = strlen(tl); for (int i = 0; i < n; i++) tp[q - n + i] = tl[i] - '0'; }
    int lo = base, hi = q - 1, h = base, s = 3, ev = 0, res = 0; long k = 0;
    for (;;) {
      int y = tp[h], ns = S[s][y];
      if (ns < 0) { res = 1; break; }
      tp[h] = W[s][y]; h += D[s][y]; s = ns; k++;
      if (h > hi) { hi = h; if (hi > CAP - 8) { res = 3; break; } }
      if (h < lo) { lo = h; if (lo < 8) { res = 3; break; }
        if (s == 1) { ev++; if (MAXEV && ev >= MAXEV) { res = 2; break; } }
        if (s == 3) { int n = 0; while (tp[h + 1 + n]) n++;
          if (n > BL + 1) { int d = (n - BL) & ~1; for (int i = 0; i <= d; i++) tp[h + i] = 0; h += d; lo = h; } } }
      if (k > 4000000000L) { res = 4; break; }
    }
    if (res == 1) { hist[ev < 4095 ? ev : 4095]++; int r = 0; for (int i = h + 1; i <= hi; i++) r += tp[i] != 0; right[r < 63 ? r : 63]++; }
    else if (res == 2) lim++; else if (res == 3) full++; else capped++;
  }
  long tot = 0; for (int i = 0; i < 4096; i++) tot += hist[i];
  printf("%s L=%d lone=%d block=%d: %ld of %ld trials halt, %ld reach %d events, %ld fill the tape, %ld pass 4e9 steps\n", m, L, lone, BL, tot, T, lim, MAXEV, full, capped);
  printf("  events before the halt:"); for (int i = 0; i < 4096; i++) if (hist[i]) printf(" %d:%ld", i, hist[i]);
  printf("\n  non-blank cells right of the head at the halt:"); for (int i = 0; i < 64; i++) if (right[i]) printf(" %d:%ld", i, right[i]); printf("\n");
  return 0;
}
