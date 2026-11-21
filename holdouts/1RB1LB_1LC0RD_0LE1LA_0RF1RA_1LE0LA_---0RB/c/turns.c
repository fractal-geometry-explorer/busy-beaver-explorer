/* The tape at every left turn: ./turns N LAST. Runs 1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB from blank for N steps;
   each time the head turns right within 4 cells of the left end it tokenizes the tape (greedy 111 = x, 110 = y,
   10 = T, 0 = o, from the leftmost 1) and prints: step  ntokens  <the last LAST tokens>.
   Every deep sweep (one that reaches a bulk 10) shows up as a change between two lines.  Used by py/defect_life.py. */
#include <stdio.h>
#include <stdlib.h>
int W[6][2], D[6][2], S[6][2];
int main(int argc, char **argv) {
  const char *T = "1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB";
  for (int i = 0; i < 6; i++) for (int r = 0; r < 2; r++) {
    const char *g = T + 7 * i + 3 * r;
    if (g[0] == '-') { S[i][r] = -1; continue; }
    W[i][r] = g[0] - '0'; D[i][r] = g[1] == 'R' ? 1 : -1; S[i][r] = g[2] - 'A';
  }
  long N = atol(argv[1]); int last = atoi(argv[2]);
  long SZ = 1L << 24; unsigned char *t = calloc(SZ, 1); long p = SZ / 2, lo = p, hi = p; int s = 0, pd = 0;
  char *buf = malloc(SZ);
  for (long k = 0; k < N; k++) {
    int r = t[p];
    if (S[s][r] < 0) { printf("HALT %ld\n", k); return 0; }
    t[p] = W[s][r]; int d = D[s][r]; s = S[s][r]; p += d;
    if (p > hi) hi = p;
    if (p < lo) lo = p;
    if (d == 1 && pd == -1 && p <= lo + 4) {
      long h = hi, x = lo, n = 0;
      while (h > lo && t[h] == 0) h--;
      while (x < h && t[x] == 0) x++;
      while (x < h) {
        if (t[x] && t[x + 1] && t[x + 2]) { buf[n++] = 'x'; x += 3; }
        else if (t[x] && t[x + 1]) { buf[n++] = 'y'; x += 3; }
        else if (t[x]) { buf[n++] = 'T'; x += 2; }
        else { buf[n++] = 'o'; x += 1; }
      }
      buf[n] = 0;
      printf("%ld %ld %s\n", k, n, n > last ? buf + n - last : buf);
    }
    pd = d;
  }
  return 0;
}
