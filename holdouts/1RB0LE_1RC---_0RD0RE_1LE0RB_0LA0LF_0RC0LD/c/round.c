// round MACHINE STATE PREFIX WORD SUFFIX < lines "MAXSTEPS TAPE"
// For each line: start in STATE on the first cell of TAPE (blank elsewhere) and run to the next *node*: the head has
// just moved left into STATE onto a cell at or left of every cell seen so far, and the tape from the head on reads
// PREFIX WORD^k SUFFIX ... with k >= 1.  Prints "NODE steps tape" (tape from the head, trailing zeros cut),
// "HALT steps" or "END".      gcc -O2 -o round round.c
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1L << 24)
static int W[6][2], Mv[6][2], Nx[6][2];
static unsigned char t[N];
static char line[1 << 22];
int main(int c, char **v) {
  if (c < 6) return 1;
  char *m = v[1]; int ev = v[2][0] - 'A';
  char *pre = v[3], *wd = v[4], *suf = v[5];
  long lp = strlen(pre), lw = strlen(wd), ls = strlen(suf);
  for (int i = 0; i < 6; i++) for (int b = 0; b < 2; b++) {
    char *p = m + i * 7 + b * 3;
    if (p[2] == '-') Nx[i][b] = -1; else { W[i][b] = p[0] - '0'; Mv[i][b] = p[1] == 'R' ? 1 : -1; Nx[i][b] = p[2] - 'A'; }
  }
  while (fgets(line, sizeof line, stdin)) {
    char *sp = strchr(line, ' '); if (!sp) continue;
    long long max = atoll(line); char *tp = sp + 1; long L = strcspn(tp, "\r\n");
    memset(t, 0, N);
    long h = N / 2, lo = h, hi = h + L; int s = ev; int done = 0;
    for (long i = 0; i < L; i++) t[h + i] = tp[i] - '0';
    for (long long k = 1; k <= max && !done; k++) {
      int b = t[h]; if (Nx[s][b] < 0) { printf("HALT %lld\n", k - 1); done = 1; break; }
      int mv = Mv[s][b]; t[h] = W[s][b]; h += mv; s = Nx[s][b];
      if (h > hi) hi = h;
      if (h < 64 || h > N - 64) { printf("OUT\n"); done = 1; break; }
      if (mv < 0 && h <= lo) {
        lo = h;
        if (s == ev) {
          long p = h, ok = 1, kk = 0;
          for (long i = 0; i < lp && ok; i++) if (t[p + i] != pre[i] - '0') ok = 0;
          p += lp;
          while (ok) { int eq = 1; for (long i = 0; i < lw; i++) if (t[p + i] != wd[i] - '0') { eq = 0; break; } if (!eq) break; p += lw; kk++; }
          if (ok && kk >= 1) { for (long i = 0; i < ls && ok; i++) if (t[p + i] != suf[i] - '0') ok = 0; } else ok = 0;
          if (ok) {
            long e = hi; while (e > h && !t[e]) e--;
            printf("NODE %lld ", k);
            for (long i = h; i <= e; i++) putchar('0' + t[i]);
            putchar('\n'); done = 1;
          }
        }
      }
    }
    if (!done) printf("END\n");
    fflush(stdout);
  }
  return 0;
}
