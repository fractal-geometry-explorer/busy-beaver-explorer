// at: plain simulator.  at MACHINE STEP1 STEP2 ...  (increasing step counts)
// Runs the machine from blank tape and prints, at exactly each of these step counts, one line:
//   STEP STATE HEAD TAPE      HEAD = offset of the head from the leftmost visited cell, TAPE = the visited cells.
// Used by py/closure/screen.py to compare the accelerated simulator with a bit-level run.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define N (1 << 27)
static uint8_t *tape;
int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: at MACHINE STEP1 STEP2 ...\n"); return 2; }
  const char *m = argv[1];
  int W[6][2], D[6][2], S[6][2];
  for (int s = 0; s < 6; s++) for (int b = 0; b < 2; b++) {
    const char *p = m + s * 7 + b * 3;
    if (p[0] == '-') { W[s][b] = 1; D[s][b] = 1; S[s][b] = 6; }
    else { W[s][b] = p[0] - '0'; D[s][b] = p[1] == 'R' ? 1 : -1; S[s][b] = p[2] - 'A'; }
  }
  tape = calloc(N, 1);
  long pos = N / 2, lo = pos, hi = pos; int st = 0; uint64_t t = 0;
  for (int a = 2; a < argc; a++) {
    uint64_t T = strtoull(argv[a], 0, 10);
    while (t < T) {
      int b = tape[pos]; int ns = S[st][b];
      if (ns == 6) { printf("HALT %llu\n", (unsigned long long)t); return 0; }
      tape[pos] = W[st][b]; pos += D[st][b]; st = ns; t++;
      if (pos < lo) lo = pos;
      if (pos > hi) hi = pos;
      if (pos < 8 || pos > N - 8) { fprintf(stderr, "tape full\n"); return 1; }
    }
    printf("%llu %c %ld ", (unsigned long long)t, 'A' + st, pos - lo);
    for (long i = lo; i <= hi; i++) putchar('0' + tape[i]);
    putchar('\n'); fflush(stdout);
  }
  return 0;
}
