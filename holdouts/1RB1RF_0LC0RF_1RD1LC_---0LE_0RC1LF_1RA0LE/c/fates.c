// fates.c: exhaustive fate of every tape B(x, y) with n = 2x + y <= M under the rule map of
// 1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE.  Fate = halting level (n of the halting tape), or the first tape above level M.
#include <stdio.h>
//   ./fates M ex.bin hl.bin     ex: per tape 0 = halts, else an id of the first tape above level M; hl: the level of the
//                              halting tape.  Layout: levels n = 2..M, per level x = 1..n/2 (y = n - 2x), 4 bytes each.
// The map is `op` of py/rules.py (and lean/Tent.lean), with B(x, 2x + 2) -> B(2x + 1, 0) -> B(2, 4x + 2) taken as one rule.
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint32_t u32; typedef int64_t i64;
static i64 M; static u32 **ex; static u32 **hl;   // ex[n][x]: exit id (0 = halts, 0xFFFFFFFF = outside); hl[n][x]: halting level
// one rule; returns 0 halt, 1 ok, 2 outside
static int op(i64 x, i64 y, i64 *X, i64 *Y) {
  if (x == 1 && y == 1) return 2;
  if (y == 2 * x + 1) return 0;
  if (y == 2 * x + 2) { *X = 2; *Y = 4 * x + 2; return 1; }          // via B(2x + 1, 0)
  if (y == 2 * x - 1) { *X = 2; *Y = 4 * x - 2; return 1; }
  if (y % 2 == 0) { i64 h = y / 2; if (x >= h) { *X = 2 * h + 2; *Y = 2 * x - 2 * h; } else { *X = 2 * x + 2; *Y = 2 * h - 2 * x - 3; } return 1; }
  { i64 h = (y - 1) / 2; if (x > h + 1) { *X = 2 * h + 4; *Y = 2 * x - 2 * h - 4; } else { *X = 2 * x + 2; *Y = 2 * h - 2 * x - 2; } return 1; }
}
int main(int argc, char **argv) {
  M = atoll(argv[1]);
  ex = malloc((M + 1) * sizeof *ex); hl = malloc((M + 1) * sizeof *hl);
  for (i64 n = M; n >= 2; n--) {
    i64 K = n / 2; ex[n] = malloc((K + 1) * 4); hl[n] = malloc((K + 1) * 4);
    for (i64 x = 1; x <= K; x++) {
      i64 y = n - 2 * x, X, Y; int r = op(x, y, &X, &Y);
      if (r == 0) { ex[n][x] = 0; hl[n][x] = n; continue; }
      if (r == 2) { ex[n][x] = 0xFFFFFFFFu; hl[n][x] = 0; continue; }
      i64 N = 2 * X + Y;
      if (N <= n) { fprintf(stderr, "level not increasing %lld %lld\n", (long long)x, (long long)y); return 1; }
      if (N > M) { ex[n][x] = (u32)((N - M - 1) * (M + 8) + X + 1); hl[n][x] = 0; }
      else { ex[n][x] = ex[N][X]; hl[n][x] = hl[N][X]; }
    }
  }
  FILE *f = fopen(argv[2], "wb");
  for (i64 n = 2; n <= M; n++) { fwrite(ex[n] + 1, 4, n / 2, f); }
  fclose(f); f = fopen(argv[3], "wb");
  for (i64 n = 2; n <= M; n++) { fwrite(hl[n] + 1, 4, n / 2, f); }
  fclose(f);
  return 0;
}
