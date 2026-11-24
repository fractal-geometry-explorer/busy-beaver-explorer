/* activezone: where 1RB1LD_1RC0RC_1LD0RE_0LB0LA_0RF1LA_---1RC changes its tape.
 *
 *   activezone STEPS EVERY
 *
 * A round trip ends when the head has visited two new cells on the right since the last one (the right end gains
 * two cells per trip).  At every EVERY-th trip the program compares the tape with the tape at the end of the
 * previous trip and prints: step, tape width, t = the trip's turning point (leftmost cell visited, from the left end
 * of the tape), z = the last cell (from the left end) that is not the previous tape shifted right by exactly two
 * cells, and z - t.  Cells left of t are untouched by construction; cells right of z moved rigidly by two.  So the
 * only cells a trip really rewrites lie in [t, z].
 * Build: gcc -O3 -o activezone activezone.c      Trust level: trusted computation (our C), observations only.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static const char *TM = "1RB1LD_1RC0RC_1LD0RE_0LB0LA_0RF1LA_---1RC";
static int W[6][2], D[6][2], NX[6][2];
int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: activezone STEPS EVERY\n"); return 2; }
  long long S = atoll(argv[1]), every = atoll(argv[2]);
  for (int s = 0; s < 6; s++) for (int b = 0; b < 2; b++) {
    const char *t = TM + 7 * s + 3 * b;
    if (t[2] == '-') { NX[s][b] = -1; continue; }
    W[s][b] = t[0] - '0'; D[s][b] = t[1] == 'R' ? 1 : -1; NX[s][b] = t[2] - 'A';
  }
  long SZ = 1L << 25; unsigned char *tape = calloc(SZ, 1), *old = calloc(SZ, 1);
  long p = SZ / 2, lo = p, hi = p, mn = p, ohi = p; int st = 0, have = 0; long long trips = 0;
  for (long long i = 0; i < S; i++) {
    int b = tape[p];
    if (NX[st][b] < 0) { printf("HALT at step %lld\n", i); return 0; }
    tape[p] = W[st][b]; p += D[st][b]; st = NX[st][b];
    if (p < lo) lo = p;
    if (p < mn) mn = p;
    if (p > hi) {
      hi = p;
      if (hi - ohi >= 2 || !have) {
        trips++;
        if (have && trips % every == 0) {
          long z = hi - 1; while (z > mn && tape[z] == old[z - 2]) z--;
          printf("%lld %ld %ld %ld %ld\n", i + 1, hi - lo, mn - lo, z - lo, z - mn); fflush(stdout);
        }
        memcpy(old + lo, tape + lo, hi - lo + 1); have = 1; ohi = hi; mn = p;
      }
    }
  }
  return 0;
}
