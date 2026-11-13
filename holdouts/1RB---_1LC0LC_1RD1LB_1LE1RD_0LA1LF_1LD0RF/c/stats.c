/* stats.c: the block rules of 1RB---_1LC0LC_1RD1LB_1LE1RD_0LA1LF_1LD0RF against the real run.
 *   stats MACHINE STEPS FROM
 * Runs the machine STEPS steps from blank tape and, from step FROM on, counts
 *  - the parity of the head's cell (relative to the start cell) for every (state, symbol read);
 *  - every start of a pass to the right (C reads 0, then D one cell to the right), by the rule of lean/Rules.lean
 *    that applies: the length of the next block (1: r_bounce, 2: r_merge, 3, 4, >= 5: r_step), "D on 0" (the head
 *    turned with B on the leftmost 1 of a block), "end" (the next block touches the right end of the tape);
 *  - every moment B reads the leftmost 1 of a block (a 0 on its left), by the number of 0s on its left: exactly
 *    four 0s is the only way to the halting transition (halt4);
 *  - for every power of two 2^k: how close the head came to the right end of the tape during steps [2^k, 2^(k+1)).
 */
#include <stdio.h>
#include <stdlib.h>
#define SZ (1 << 27)
static unsigned char tape[SZ];
int main(int c, char **v) {
  if (c < 4) { fprintf(stderr, "usage: stats MACHINE STEPS FROM\n"); return 2; }
  const char *m = v[1]; long long N = atoll(v[2]), FROM = atoll(v[3]);
  int w[6][2], d[6][2], n[6][2];
  for (int i = 0; i < 6; i++) for (int s = 0; s < 2; s++) {
    const char *x = m + 7 * i + 3 * s;
    if (x[2] == '-') { n[i][s] = -1; continue; }
    w[i][s] = x[0] - '0'; d[i][s] = x[1] == 'R' ? 1 : -1; n[i][s] = x[2] - 'A';
  }
  long h = SZ / 2, lo = h, hi = h; int st = 0; long long t = 0;
  static long long P[6][2][2], PL[6][2][2], G[64], GL[64], K[8], KL[8];
  long long nextp = 1024; long mx = h;
  for (; t < N;) {
    if (h < lo) lo = h; if (h > hi) hi = h;
    if (h > mx) mx = h;
    if (t == nextp) { printf("reach steps<%lld cells %ld closest_to_right_end %ld\n", nextp, hi - lo + 1, hi - mx); nextp *= 2; mx = h; }
    int s = tape[h];
    if (t >= FROM) {
      P[st][s][h & 1]++; PL[st][s][h & 1] = t;
      if (st == 1 && s == 1 && tape[h - 1] == 0) {
        long g = 0, x = h - 1; while (x >= lo && tape[x] == 0 && g < 60) { g++; x--; }
        if (x < lo) g = 61; G[g]++; GL[g] = t;
      }
      if (st == 2 && s == 0) {
        int k;
        if (tape[h + 1] == 0) k = 0;
        else {
          long p = h + 1; while (tape[p]) p++;
          long q = p + 1; while (q <= hi && tape[q]) q++;
          long b = q - p - 1;
          k = q > hi ? 6 : b >= 5 ? 5 : (int)b;
          if (b == 0) k = 6;
        }
        K[k]++; KL[k] = t;
      }
    }
    if (n[st][s] < 0) { printf("HALT %lld\n", t); return 0; }
    tape[h] = w[st][s]; h += d[st][s]; st = n[st][s]; t++;
  }
  printf("steps %lld from %lld cells %ld\n", N, FROM, hi - lo + 1);
  for (int i = 0; i < 6; i++) for (int s = 0; s < 2; s++)
    printf("parity %c%d even %lld last %lld odd %lld last %lld\n", 'A' + i, s, P[i][s][0], PL[i][s][0], P[i][s][1], PL[i][s][1]);
  const char *nm[] = {"D_on_0", "bounce_1", "merge_2", "step_3", "step_4", "step_ge5", "end"};
  for (int k = 0; k < 7; k++) printf("pass %s %lld last %lld\n", nm[k], K[k], KL[k]);
  for (int g = 0; g < 64; g++) if (G[g]) printf("B_leftmost zeros %d%s count %lld last %lld\n", g, g == 60 ? "+" : g == 61 ? " (blank)" : "", G[g], GL[g]);
  return 0;
}
