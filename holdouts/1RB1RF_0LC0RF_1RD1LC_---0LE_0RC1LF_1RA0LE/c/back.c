// back.c: ancestors of every halting tape B(x, 2x + 1) of 1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE under the rule map.
// For the octave [L, 2L): every halting tape with level m = 2x + y in [L, 2L); its ancestors are followed down to
// level L/2.  Prints, per halting tape with at least one ancestor in levels [L/2, L): its count there (all, x even).
//   ./back L [T]     T: only print tapes with at least T ancestors in [L/2, L)   (default 1)
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef int64_t i64;
static i64 L, lo, hi, cnt, cnte, nodes;
static i64 sx[1 << 24], sy[1 << 24];
static void anc(i64 X, i64 Y) {       // iterative DFS over preimages
  int sp = 0; sx[sp] = X; sy[sp] = Y; sp++;
  while (sp) {
    sp--; X = sx[sp]; Y = sy[sp]; nodes++;
    i64 n = 2 * X + Y;
    if (n < L) { cnt++; if (X % 2 == 0) cnte++; }
#define PUSH(a, b) do { i64 a_ = (a), b_ = (b); if (a_ >= 1 && 2 * a_ + b_ >= lo && !(a_ == 1 && b_ == 1)) { sx[sp] = a_; sy[sp] = b_; sp++; } } while (0)
    if (X % 2) continue;                                      // odd x: no rule leads here (B(odd, 0) is passed inside a rule)
    if (X == 2 && Y % 4 == 2 && Y >= 6) { PUSH((Y - 2) / 4, (Y - 2) / 2 + 2); PUSH((Y + 2) / 4, (Y + 2) / 2 - 1); }
    if (Y % 2 == 0) {
      i64 h = (X - 2) / 2; PUSH(Y / 2 + h, 2 * h);                           // fold, y even
      if (X >= 4) { h = (X - 4) / 2; PUSH(Y / 2 + h + 2, 2 * h + 1); }       // fold, y odd
      if (X >= 4) { i64 x = (X - 2) / 2; PUSH(x, Y + 2 * x + 3); }           // double, y odd
    } else {
      if (X >= 4) { i64 x = (X - 2) / 2; PUSH(x, Y + 2 * x + 3); }           // double, y even
    }
  }
}
int main(int argc, char **argv) {
  L = atoll(argv[1]); i64 T = argc > 2 ? atoll(argv[2]) : 1; lo = L / 2; hi = 2 * L;
  i64 tot = 0, tote = 0, ev = 0, hs = 0;
  for (i64 x = 1; 4 * x + 1 < hi; x++) {
    i64 m = 4 * x + 1; if (m < L) continue;
    cnt = cnte = 0; hs++; anc(x, 2 * x + 1);
    tot += cnt; tote += cnte; if (cnt) ev++;
    if (cnt >= T) printf("halt B(%lld, %lld) level %lld ancestors in [L/2, L): %lld (x even %lld)\n", (long long)x, (long long)(2 * x + 1), (long long)m, (long long)cnt, (long long)cnte);
  }
  // population of [L/2, L): sum over n of floor(n/2); x even: floor(n/4)
  i64 pop = 0, pope = 0; for (i64 n = lo; n < L; n++) { pop += n / 2; pope += n / 4; }
  printf("octave %lld: halting tapes %lld, with an ancestor in [L/2, L) %lld; halting fraction of [L/2, L): all %.5f, x even %.5f; nodes %lld\n",
         (long long)L, (long long)hs, (long long)ev, (double)tot / pop, (double)tote / pope, (long long)nodes);
  return 0;
}
