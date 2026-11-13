/* The left end of 1RB0RC_1RC1LB_1LD1RA_1LE0LB_---1LF_0LF0LC from blank tape.
   For each new leftmost cell: the step, the width, and the closest F came to the left end since the previous one.
   At the end: how often the leftmost cell held 0 while the head was to its right (expected: never), and how often F
   stood on the second cell (it must read a 1 there; F reading a 1 on the leftmost cell halts three steps later).
   usage: cc -O2 -o leftedge leftedge.c && ./leftedge STEPS */
#include <stdio.h>
#include <stdlib.h>
#define N (1L << 26)
static unsigned char t[N];
int main(int argc, char **argv) {
  const char *m = "1RB0RC_1RC1LB_1LD1RA_1LE0LB_---1LF_0LF0LC";
  int W[6][2], Mv[6][2], S[6][2];
  long long max = argc > 1 ? atoll(argv[1]) : 1000000000LL;
  for (int s = 0; s < 6; s++)
    for (int y = 0; y < 2; y++) {
      const char *p = m + 7 * s + 3 * y;
      if (p[0] == '-') { S[s][y] = -1; continue; }
      W[s][y] = p[0] - '0'; Mv[s][y] = p[1] == 'R' ? 1 : -1; S[s][y] = p[2] - 'A';
    }
  long h = N / 2, lo = h, hi = h, minF = -1;
  int st = 0;
  long long i, bad = 0, f2 = 0;
  for (i = 0; i < max; i++) {
    int y = t[h], ns = S[st][y];
    if (ns < 0) { printf("HALT after %lld steps\n", i + 1); return 0; }
    t[h] = W[st][y]; h += Mv[st][y]; st = ns;
    if (h < 2 || h > N - 3) { printf("tape full at %lld\n", i); return 1; }
    if (h < lo) { printf("new left end at step %lld, width %ld, closest F since the last one: leftmost + %ld (-1: none)\n", i + 1, hi - lo + 1, minF); lo = h; minF = -1; }
    if (h > hi) hi = h;
    if (h > lo && t[lo] != 1) bad++;
    if (st == 5) { if (minF < 0 || h - lo < minF) minF = h - lo; if (h == lo + 1) f2++; }
  }
  printf("%lld steps, no halt; leftmost cell 0 with the head right of it: %lld times; F on the second cell: %lld times\n", i, bad, f2);
  return 0;
}
