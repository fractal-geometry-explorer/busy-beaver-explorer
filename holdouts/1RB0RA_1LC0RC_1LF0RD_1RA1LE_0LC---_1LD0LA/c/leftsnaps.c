/* leftsnaps: the tape of 1RB0RA_1LC0RC_1LF0RD_1RA1LE_0LC---_1LD0LA each time the head extends the tape on the left
 * in state D (once per sweep), as a line "step D cells" (cells from the left end).
 *
 *   leftsnaps STEPS > snaps.txt        then  python3 py/levels.py snaps.txt
 * Build: gcc -O3 -o leftsnaps leftsnaps.c        Trust level: trusted computation (our C).
 */
#include <stdio.h>
#include <stdlib.h>
static const char *TM = "1RB0RA_1LC0RC_1LF0RD_1RA1LE_0LC---_1LD0LA";
static int W[6][2], D[6][2], NX[6][2];
int main(int argc, char **argv) {
  long long S = argc > 1 ? atoll(argv[1]) : 100000000;
  for (int s = 0; s < 6; s++) for (int b = 0; b < 2; b++) {
    const char *t = TM + 7 * s + 3 * b;
    if (t[2] == '-') { NX[s][b] = -1; continue; }
    W[s][b] = t[0] - '0'; D[s][b] = t[1] == 'R' ? 1 : -1; NX[s][b] = t[2] - 'A';
  }
  long SZ = 1L << 26; unsigned char *tape = calloc(SZ, 1); long p = SZ / 2, lo = p, hi = p; int st = 0;
  for (long long i = 0; i < S; i++) {
    int b = tape[p];
    if (NX[st][b] < 0) { printf("HALT %lld\n", i); return 0; }
    tape[p] = W[st][b]; p += D[st][b]; st = NX[st][b];
    if (p > hi) hi = p;
    if (p < lo) {
      lo = p;
      if (st == 3) { printf("%lld D ", i + 1); for (long q = lo; q <= hi; q++) putchar('0' + tape[q]); putchar('\n'); }
    }
  }
  return 0;
}
