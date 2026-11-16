/* z1: the old zone alone, exact while the stranded block lasts (see the README, "Two zones").
 *
 *   z1 STATE [MINP] [SHOW]
 *
 * STATE as for xs.c.  Finds the first stretch of Z of period 3 and at least MINP letters (default 1000), the
 * stranded block P, and runs the sweep on P ++ (the rest) by itself, one *tick* per pass through the new zone
 * (lean/Xor.lean, `swr_split`: what such a pass does beyond the new zone depends only on P ++ the rest).  Each tick
 * shortens the word by one letter at its head end, the end next to the new zone; the run stops when P is used up.
 * Reports a reset (no 00 left), a halt, or the end of P, and with SHOW the last 60 letters after each of the first
 * SHOW ticks (to compare with `xs ... DEEP`).  Build: gcc -O2 -o z1 z1.c */
#include <stdio.h>
#include <stdlib.h>
int main(int c, char **v) {
  if (c < 2) { fprintf(stderr, "usage: z1 STATE [MINP] [SHOW]\n"); return 2; }
  FILE *f = fopen(v[1], "r"); unsigned long long t, n; long rl;
  if (!f || fscanf(f, "%llu %llu %ld ", &t, &n, &rl) != 3) { fprintf(stderr, "bad state\n"); return 2; }
  unsigned char *Z = malloc(1 << 24); long L = 0; int ch;
  while ((ch = fgetc(f)) == '0' || ch == '1') Z[L++] = ch - '0';
  long MINP = c > 2 ? atol(v[2]) : 1000, show = c > 3 ? atol(v[3]) : 0, s0 = -1;
  for (long i = 0; i + MINP < L && s0 < 0; i++) {
    long j = i; while (j + 3 < L && Z[j + 3] == Z[j]) j++;
    if (j - i >= MINP) s0 = i;
  }
  if (s0 < 0) { printf("no block\n"); return 1; }
  long pe = s0; while (pe + 3 < L && Z[pe + 3] == Z[pe]) pe++; pe += 3;
  printf("block: letters %ld to %ld of Z (%ld letters); old zone %ld letters\n", s0, pe, pe - s0, L - pe);
  unsigned char *a = Z + s0; long len = L - s0, P = pe - s0, low = -1;
  for (long tick = 1; tick <= P; tick++) {
    long k = -1;
    for (long j = 0; j + 1 < len; j++) if (!a[j] && !a[j + 1]) { k = j; break; }
    if (k < 0) { printf("RESET in tick %ld (%ld letters of the block left)\n", tick, P - tick + 1); return 0; }
    if (k + 2 >= len) { printf("HALT in tick %ld (%ld letters of the block left)\n", tick, P - tick + 1); return 0; }
    if (k < P - tick) { printf("tick %ld: a 00 inside the block\n", tick); return 0; }
    if (low < 0 || len - 1 - k < low) { low = len - 1 - k; printf("tick %ld: 00 at %ld letters from the left end\n", tick, low); }
    for (long j = k - 1; j >= 0; j--) a[j + 1] ^= a[j];
    a[k + 2] ^= 1; a++; len--;
    if (tick <= show) {
      printf("tick %ld ", tick);
      for (long j = len - 60; j < len; j++) putchar('0' + a[j]);
      putchar('\n');
    }
  }
  printf("block used up after %ld ticks, no reset and no halt\n", P);
  return 0;
}
