/* xs: the XOR sweep of lean/Xor.lean (`swr`) on the zone orbit of lean/Zone.lean, from a state written by
 * lean/DumpState.lean, for the four machines with the `111110` block (1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA,
 * 1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA, 1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA,
 * 1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB).
 *
 *   xs STATE SWEEPS [DEEP]
 *
 * STATE is "t n 0 Z": the step count, the block count n and the reversed word Z after the block (head side first).
 * One sweep is `cstep` of lean/Zone.lean at the right end: the letter pat n = (n mod 3 != 2) in front of Z, the
 * first 00 of that word, the letter after it flipped, the letters before it replaced by XOR differences, n + 1.
 * Stops at a reset (no 00: the machine's own reset rule is needed, see lean/Sweep.lean) or a halt.
 * Prints the depth records (where the 00 was found), with DEEP every sweep deeper than DEEP letters and the last 60
 * letters of Z after it (the leftmost cells of the tape, read right to left), and a histogram of depths.
 * Build: gcc -O2 -o xs xs.c */
#include <stdio.h>
#include <stdlib.h>
int main(int c, char **v) {
  if (c < 3) { fprintf(stderr, "usage: xs STATE SWEEPS [DEEP]\n"); return 2; }
  FILE *f = fopen(v[1], "r"); unsigned long long t, n; long rl;
  if (!f || fscanf(f, "%llu %llu %ld ", &t, &n, &rl) != 3 || rl != 0) { fprintf(stderr, "bad state\n"); return 2; }
  unsigned char *Z = malloc(1 << 24); long L = 0; int ch;
  while ((ch = fgetc(f)) == '0' || ch == '1') Z[L++] = ch - '0';
  long long S = atof(v[2]), deep = c > 3 ? atol(v[3]) : -1, maxk = -1, hist[64] = {0};
  for (long long s = 1; s <= S; s++) {
    unsigned char cc = (n % 3) != 2;          /* pat n, the letter of the block next to Z */
    long k = -1;                              /* the 00 is at letters k, k+1 of cc :: Z */
    if (cc == 0 && Z[0] == 0) k = 0;
    else for (long j = 1; j < L; j++) if (Z[j - 1] == 0 && Z[j] == 0) { k = j; break; }
    if (k < 0) { printf("RESET at sweep %lld (n = %llu)\n", s, n); break; }
    if (k + 1 >= L) { printf("HALT at sweep %lld\n", s); break; }
    Z[k + 1] ^= 1;                            /* the letter after the 00 */
    for (long j = k - 1; j >= 1; j--) Z[j] ^= Z[j - 1];
    if (k >= 1) Z[0] ^= cc;                   /* XOR differences before it */
    n++;
    int b = 0; while ((1LL << (b + 1)) <= k + 1) b++; hist[b]++;
    if (k > maxk) { maxk = k; printf("sweep %lld: depth record %ld (%ld letters from the left end)\n", s, k, L - 1 - k); }
    if (deep >= 0 && k > deep) {
      printf("deep %lld %ld ", s, L - 1 - k);
      for (long j = L - 60; j < L; j++) putchar('0' + Z[j]);
      putchar('\n');
    }
    fflush(stdout);
  }
  printf("n = %llu\n", n);
  for (int b = 0; b < 40; b++) if (hist[b]) printf("depth in [%lld, %lld): %lld\n", (1LL << b) - 1, (1LL << (b + 1)) - 1, hist[b]);
  return 0;
}
