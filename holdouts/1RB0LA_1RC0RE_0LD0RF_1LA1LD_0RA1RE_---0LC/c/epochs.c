// epochs MACHINE MAXSTEPS [TAPE] : run from blank tape (or from A> TAPE, blank elsewhere) and print every left-A record
// (head on a new leftmost cell in state A) whose tape is (01111)^m followed by at most 60 cells, with m >= 20:
// the step, m and those cells (the "tail").   gcc -O2 -o epochs epochs.c
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1L << 28)
int W[6][2], Mv[6][2], Nx[6][2];
int main(int c, char **v) {
  if (c < 3) { fprintf(stderr, "usage: epochs MACHINE MAXSTEPS [TAPE]\n"); return 1; }
  char *m = v[1];
  for (int i = 0; i < 6; i++) for (int b = 0; b < 2; b++) {
    char *p = m + i * 7 + b * 3;
    if (p[2] == '-') Nx[i][b] = -1; else { W[i][b] = p[0] - '0'; Mv[i][b] = p[1] == 'R' ? 1 : -1; Nx[i][b] = p[2] - 'A'; }
  }
  long long max = atoll(v[2]); unsigned char *t = calloc(N, 1); long h = N / 2, lo = h, hi = h; int s = 0;
  if (c > 3) { long L = strlen(v[3]); for (long i = 0; i < L; i++) t[h + i] = v[3][i] - '0'; hi = h + L - 1; }
  static const unsigned char blk[5] = {0, 1, 1, 1, 1};
  for (long long k = 1; k <= max; k++) {
    int b = t[h]; if (Nx[s][b] < 0) { printf("HALT %lld\n", k); return 0; }
    t[h] = W[s][b]; h += Mv[s][b]; s = Nx[s][b];
    if (h > hi) hi = h;
    if (h < lo) {
      lo = h;
      if (h < 64 || hi > N - 64) { printf("OUT OF TAPE at %lld\n", k); return 1; }
      if (s == 0) {
        long p = h, mm = 0;
        while (p + 5 <= hi + 1 && !memcmp(t + p, blk, 5)) { p += 5; mm++; }
        long e = hi; while (e >= p && !t[e]) e--;
        if (mm >= 20 && e - p + 1 <= 60) {
          printf("%lld %ld ", k, mm); for (long i = p; i <= e; i++) putchar('0' + t[i]); putchar('\n'); fflush(stdout);
        }
      }
    }
  }
  printf("END %lld\n", max);
}
