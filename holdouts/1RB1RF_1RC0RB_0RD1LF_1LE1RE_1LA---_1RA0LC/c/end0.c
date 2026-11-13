/* Count, in the run of 1RB1RF_1RC0RB_0RD1LF_1LE1RE_1LA---_1RA0LC from blank tape, the steps where the configuration
   has the shape of the start of absorb0 (state C on 1 0 0 1 0 1 0, left of it 1^(8u+4) then 0 0 1) and of the E frame
   of lean/ChainEnd.lean (state C, left 1 0 1 0, right (10)^(k+1) 1 1 0 1 0 1 0).
   usage: cc -O2 -o end0 end0.c && ./end0 STEPS */
#include <stdio.h>
#include <stdlib.h>
int W[6][2], Mv[6][2], N[6][2];
int main(int c, char **v) {
  const char *M = "1RB1RF_1RC0RB_0RD1LF_1LE1RE_1LA---_1RA0LC";
  for (int s = 0; s < 6; s++) for (int b = 0; b < 2; b++) {
    const char *g = M + 7 * s + 3 * b;
    if (g[0] == '-') { N[s][b] = -1; continue; }
    W[s][b] = g[0] - '0'; Mv[s][b] = g[1] == 'R' ? 1 : -1; N[s][b] = g[2] - 'A';
  }
  long long max = atoll(v[1]); int SZ = 1 << 22; char *t = calloc(SZ, 1); long p = SZ / 2; int st = 0;
  long long cntE = 0, cntA = 0, firstE = 0, firstA = 0;
  for (long long k = 1; k <= max; k++) {
    int b = t[p]; int ns = N[st][b];
    if (ns < 0) { printf("HALT %lld\n", k); return 0; }
    t[p] = W[st][b]; p += Mv[st][b]; st = ns;
    if (st != 2) continue;
    if (t[p] == 1 && t[p+1] == 0 && t[p-1] == 1 && t[p-2] == 0 && t[p-3] == 1 && t[p-4] == 0) {
      long q = p; while (t[q] == 1 && t[q+1] == 0) q += 2;
      if (t[q] == 1 && t[q+1] == 1 && t[q+2] == 0 && t[q+3] == 1 && t[q+4] == 0 && t[q+5] == 1 && t[q+6] == 0) { cntE++; if (!firstE) firstE = k; }
    }
    if (t[p] == 1 && t[p+1] == 0 && t[p+2] == 0 && t[p+3] == 1 && t[p+4] == 0 && t[p+5] == 1 && t[p+6] == 0 && t[p-1] == 1) {
      long q = p - 1; while (t[q] == 1) q--;
      if ((p - 1 - q) % 8 == 4 && t[q] == 0 && t[q-1] == 0 && t[q-2] == 1) { cntA++; if (!firstA) firstA = k; }
    }
  }
  printf("absorb0 starts: %lld (first at step %lld); E frames: %lld (first at step %lld)\n", cntA, firstA, cntE, firstE);
  return 0;
}
