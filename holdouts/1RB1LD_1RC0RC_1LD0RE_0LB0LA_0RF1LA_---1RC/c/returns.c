/* returns: what the trips beyond a fixed cell X bring back to 1RB1LD_1RC0RC_1LD0RE_0LB0LA_0RF1LA_---1RC.
 *
 *   returns STEPS FROM X K        (X: a cell, counted from the start cell; K: cells right of X to print)
 *
 * After step FROM, each time the head crosses from X-1 to X it prints "OUT step state cells", the cells X-8 .. X+K-1,
 * and when it comes back from X to X-1, " BACK duration state cells" (same window).  py/returns.py groups the long
 * trips by what the head left behind and checks whether what it brings back is a function of that.
 * Build: gcc -O3 -o returns returns.c       Trust level: trusted computation (our C), observations.
 */
#include <stdio.h>
#include <stdlib.h>
static const char *TM = "1RB1LD_1RC0RC_1LD0RE_0LB0LA_0RF1LA_---1RC";
static int W[6][2], D[6][2], NX[6][2];
int main(int argc, char **argv) {
  if (argc < 5) { fprintf(stderr, "usage: returns STEPS FROM X K\n"); return 2; }
  long long S = atoll(argv[1]), from = atoll(argv[2]); long X = atol(argv[3]); int K = atoi(argv[4]);
  for (int s = 0; s < 6; s++) for (int b = 0; b < 2; b++) {
    const char *t = TM + 7 * s + 3 * b;
    if (t[2] == '-') { NX[s][b] = -1; continue; }
    W[s][b] = t[0] - '0'; D[s][b] = t[1] == 'R' ? 1 : -1; NX[s][b] = t[2] - 'A';
  }
  long SZ = 1L << 26; unsigned char *tape = calloc(SZ, 1); long o = SZ / 2, p = o; int st = 0, out = 0; long long t0 = 0;
  X += o;
  for (long long i = 0; i < S; i++) {
    int b = tape[p];
    if (NX[st][b] < 0) { printf("HALT %lld\n", i); return 0; }
    tape[p] = W[st][b]; long op = p; p += D[st][b]; st = NX[st][b];
    if (i < from) continue;
    if (op == X - 1 && p == X && !out) {
      out = 1; t0 = i; printf("OUT %lld %c ", i, 'A' + st); for (long q = X - 8; q < X + K; q++) putchar('0' + tape[q]);
    } else if (op == X && p == X - 1 && out) {
      out = 0; printf(" BACK %lld %c ", i - t0, 'A' + st); for (long q = X - 8; q < X + K; q++) putchar('0' + tape[q]); putchar('\n');
    }
  }
  return 0;
}
