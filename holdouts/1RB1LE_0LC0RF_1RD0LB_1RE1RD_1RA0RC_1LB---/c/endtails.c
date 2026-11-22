/* The right end of the tape at every return of the head to the left end, for py/endlayer.py.

   usage: endtails MACHINE MIRROR STEPS W
   At each return to the left end (after being more than 40 cells away) the tape is in group form.  Let X be the first
   group start (a 1 after 000) at least W cells left of the right end.  Printed, one line per round trip:
       step  state  cells
   step: the step of the return; cells: the tape from X to the right end; state: the state of the machine when the
   head next reaches X (on the following rightward sweep), which tells the slot of the group at X ('?' if it does not
   get there before the next return).  MIRROR=1 exchanges left and right. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv) {
  if (argc < 5) { fprintf(stderr, "usage: endtails MACHINE MIRROR STEPS W\n"); return 2; }
  const char *m = argv[1];
  int mir = atoi(argv[2]);
  long long steps = atoll(argv[3]);
  int W = atoi(argv[4]);
  int wr[6][2], mv[6][2], nx[6][2];
  for (int s = 0; s < 6; s++)
    for (int r = 0; r < 2; r++) {
      const char *x = m + 7 * s + 3 * r;
      if (x[2] == '-') { nx[s][r] = -1; continue; }
      wr[s][r] = x[0] - '0';
      int d = x[1] == 'R' ? 1 : -1;
      mv[s][r] = mir ? -d : d;
      nx[s][r] = x[2] - 'A';
    }
  size_t N = (size_t)1 << 26;
  uint8_t *t = calloc(N, 1);
  char *buf = malloc(1 << 20);
  long p = N / 2, lo = p, hi = p, X = -1;
  int st = 0, far = 0, waiting = 0;
  long long kk = 0;
  for (long long k = 1; k <= steps; k++) {
    int r = t[p];
    if (nx[st][r] < 0) { printf("HALT %lld\n", k); return 0; }
    t[p] = wr[st][r]; p += mv[st][r]; st = nx[st][r];
    if (p < lo) lo = p;
    if (p > hi) hi = p;
    if (p < 8 || p > (long)N - 8) { fprintf(stderr, "tape full\n"); return 1; }
    if (waiting && p == X) { printf("%lld %c %s\n", kk, 'A' + st, buf); waiting = 0; }
    if (!far && p - lo > 40) far = 1;
    else if (far && p <= lo + 6) {
      far = 0;
      if (waiting) { printf("%lld ? %s\n", kk, buf); waiting = 0; }
      long x = hi - W;
      if (x < lo + 60) x = lo + 60;
      while (x <= hi && !(t[x] == 1 && t[x - 1] == 0 && t[x - 2] == 0 && t[x - 3] == 0)) x++;
      if (x > hi) continue;
      int n = 0;
      for (long i = x; i <= hi; i++) buf[n++] = '0' + t[i];
      buf[n] = 0;
      X = x; waiting = 1; kk = k;
    }
  }
  return 0;
}
