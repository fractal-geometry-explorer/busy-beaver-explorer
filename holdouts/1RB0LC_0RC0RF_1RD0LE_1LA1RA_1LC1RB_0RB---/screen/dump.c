/* dump MACHINE MAXSTEPS T0 [RATIO]
 *
 * Plain simulation from blank tape.  After each threshold T0, T0*RATIO, ... (default ratio 2) the tape is printed at
 * the first new leftmost cell and at the first new rightmost cell:  "L|R STEP STATE LENGTH CELLS".
 * "HALT STEP" if the machine halts.  (From the G09 screen, /mnt/project-files/g09-screen/tools/dump.c.)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define N (1 << 27)
static uint8_t *tape;
int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage: dump MACHINE MAXSTEPS T0 [RATIO]\n"); return 2; }
  const char *m = argv[1];
  uint64_t maxs = strtoull(argv[2], 0, 10), thr = strtoull(argv[3], 0, 10);
  double ratio = argc > 4 ? atof(argv[4]) : 2.0;
  int W[6][2], D[6][2], S[6][2];
  for (int s = 0; s < 6; s++)
    for (int b = 0; b < 2; b++) {
      const char *p = m + s * 7 + b * 3;
      if (p[0] == '-') { W[s][b] = 1; D[s][b] = 1; S[s][b] = 6; }
      else { W[s][b] = p[0] - '0'; D[s][b] = p[1] == 'R' ? 1 : -1; S[s][b] = p[2] - 'A'; }
    }
  tape = calloc(N, 1);
  long pos = N / 2, lo = pos, hi = pos;
  int st = 0, needL = 0, needR = 0;
  uint64_t t = 0;
  while (t < maxs) {
    int b = tape[pos], ns = S[st][b];
    if (ns == 6) { printf("HALT %llu\n", (unsigned long long)t + 1); return 0; }
    tape[pos] = W[st][b]; pos += D[st][b]; st = ns; t++;
    if (pos < lo || pos > hi) {
      int left = pos < lo;
      if (left) lo = pos; else hi = pos;
      if (t >= thr) { needL = needR = 1; thr = (uint64_t)(thr * ratio) + 1; }
      if ((left && needL) || (!left && needR)) {
        if (left) needL = 0; else needR = 0;
        printf("%c %llu %c %ld ", left ? 'L' : 'R', (unsigned long long)t, 'A' + st, hi - lo + 1);
        for (long i = lo; i <= hi; i++) putchar('0' + tape[i]);
        putchar('\n'); fflush(stdout);
      }
      if (pos < 8 || pos > N - 8) { fprintf(stderr, "tape full\n"); return 1; }
    }
  }
  fprintf(stderr, "done %llu lo %ld hi %ld\n", (unsigned long long)t, lo - N / 2, hi - N / 2);
  return 0;
}
