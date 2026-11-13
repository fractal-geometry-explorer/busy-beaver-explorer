// Turns of F and double zeros in the run of 1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF from blank tape.
//
// F going right turns round at a separator followed by a block of two or more 1s (`f_turn` in lean/Blocks.lean:
// F fills the separator, A erases the block's first cell, E reads its second cell and turns).  This program counts
// those turns by the length of the block, and counts the times A reads a 0 (F found two 0s in a row), with where on
// the tape each happened.  A halt is A reading 0 followed by B reading 1 (`halt_F`).
//
// usage: turns STEPS [v]      (v: print every turn at a block of even length and every double zero)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static const char *M = "1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF";
int main(int argc, char **argv) {
  long long N = atoll(argv[1]); int show = argc > 2;
  int wr[6][2], mv[6][2], nx[6][2];
  for (int s = 0; s < 6; s++) for (int b = 0; b < 2; b++) {
    const char *t = M + s * 7 + b * 3;
    if (t[0] == '-') { nx[s][b] = -1; continue; }
    wr[s][b] = t[0] - '0'; mv[s][b] = t[1] == 'R' ? 1 : -1; nx[s][b] = t[2] - 'A';
  }
  long SZ = 1L << 27; unsigned char *tape = calloc(SZ, 1); long p = SZ / 2, lo = p, hi = p; int s = 0, prev = -1;
  long long hist[64] = {0}, turns = 0, even = 0, even_inner = 0, zz = 0, zz_inner = 0, i;
  for (i = 0; i < N; i++) {
    int b = tape[p];
    if (nx[s][b] < 0) { printf("HALT at step %lld\n", i + 1); break; }
    if (s == 4 && b == 1 && prev == 0) {            /* E reads 1 right after A: a turn; the block is p-1 .. q-1 */
      long q = p; while (tape[q]) q++;
      long len = q - p + 1; turns++; hist[len < 63 ? len : 63]++;
      if (len % 2 == 0) { even++; if (q - 1 < hi) even_inner++;
        if (show) printf("turn at a block of %ld, step %lld, block ends %ld cells before the right end\n", len, i, hi - (q - 1)); }
    }
    if (s == 0 && b == 0) {                          /* A reads 0: F had two 0s in front of it */
      zz++; if (p < hi) zz_inner++;
      if (show) printf("double zero, step %lld, A is %ld cells before the right end, next cell %d\n", i, hi - p, tape[p + 1]);
    }
    prev = s; tape[p] = wr[s][b]; p += mv[s][b]; s = nx[s][b]; if (p < lo) lo = p; if (p > hi) hi = p;
  }
  printf("steps %lld  left %ld  right %ld\n", i, SZ / 2 - lo, hi - SZ / 2);
  printf("turns of F %lld, at a block of even length %lld (not the last block of the tape: %lld)\n", turns, even, even_inner);
  printf("A read 0 %lld times (with visited cells further right: %lld)\n", zz, zz_inner);
  for (int k = 1; k < 64; k++) if (hist[k]) printf("block of %d%s: %lld\n", k, k == 63 ? " or more" : "", hist[k]);
  return 0;
}
