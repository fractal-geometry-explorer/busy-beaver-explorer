// twin M1 M2 STEPS: run two machines side by side from blank tape and check that at every step they write the same
// symbol at the same cell and move the same way (so their tapes and head positions agree at every step).
#include <stdio.h>
#include <stdlib.h>
#define N (1<<26)
static unsigned char t1[N], t2[N];
static void parse(const char *m, int nw[6][2], int mv[6][2], int ns[6][2]) {
  for (int s = 0; s < 6; s++) for (int r = 0; r < 2; r++) {
    const char *t = m + s * 7 + r * 3;
    if (t[0] == '-') { ns[s][r] = -1; continue; }
    nw[s][r] = t[0] - '0'; mv[s][r] = t[1] == 'R' ? 1 : -1; ns[s][r] = t[2] - 'A';
  }
}
int main(int argc, char **argv) {
  int nw1[6][2], mv1[6][2], ns1[6][2], nw2[6][2], mv2[6][2], ns2[6][2];
  parse(argv[1], nw1, mv1, ns1); parse(argv[2], nw2, mv2, ns2);
  long long steps = atoll(argv[3]); long p = N / 2; int s1 = 0, s2 = 0;
  for (long long i = 0; i < steps; i++) {
    int r1 = t1[p], r2 = t2[p];
    if (r1 != r2) { printf("tapes differ at step %lld\n", i); return 1; }
    int a = ns1[s1][r1], b = ns2[s2][r2];
    if (a < 0 || b < 0) { printf("halt at step %lld: %d %d\n", i, a, b); return 1; }
    if (nw1[s1][r1] != nw2[s2][r2] || mv1[s1][r1] != mv2[s2][r2]) { printf("moves differ at step %lld\n", i); return 1; }
    t1[p] = nw1[s1][r1]; t2[p] = nw2[s2][r2]; p += mv1[s1][r1]; s1 = a; s2 = b;
    if (p <= 1 || p >= N - 2) { printf("out of tape at step %lld\n", i); return 1; }
  }
  printf("same tape and head for %lld steps\n", steps);
  return 0;
}
