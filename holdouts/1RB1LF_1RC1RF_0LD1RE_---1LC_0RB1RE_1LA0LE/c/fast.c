// The right-end map of 1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE on T(c, a, b), a transcription of step() in
// py/model.py with 64-bit integers (overflow checked).  c = -1 means no bracket.
// usage: fast MAXOPS [dump N]      (gcc -O2 -o fast fast.c)
//   MAXOPS: inner operations (rounds blocks: doublings + carries) to run; prints every odd event T(c, A, 0),
//   a halt if one happens, and the final configuration.  "dump N": print the first N configurations (for tests).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long long ll;
static ll c = -1, a = 2, b = 0;          // T(None, 2, 0), reached at step 7 from blank tape
static unsigned long long ops = 0, visits = 0;
#define LIM ((ll)1 << 60)
static void norm(void) { if (c >= 0 && a == 1) { b = c + b + 1; c = -1; a = 2; } }
// one visit to the next; returns 0 on halt
static int step(void) {
  if (c < 0 && a == 1) return 0;
  ll x = a, p = 2, w = b;
  for (;;) {
    ops++;
    if (x > LIM || p > LIM || w > LIM || c > LIM) { printf("OVERFLOW\n"); exit(2); }
    if (!(x & 1)) {
      ll k = (x - 2) / 2;
      if (w <= k - 1) { a = x - 2 * w - 2; b = p / 2 + 2 * w + 1; break; }
      p += 4 * k; w -= k; x = 2;
      if (w == 0) { a = p + 3; b = 0; break; }
      if (w == 1) { a = p + 4; b = 0; break; }
      x = p + 4; p = 2; w -= 2;
    } else {
      ll k = (x - 3) / 2;
      if (w <= k) { a = x - 2 * w - 2; b = p / 2 + 2 * w + 1; break; }
      p += 4 * k; w -= k; x = 3;
      if (c < 0) {
        p += 4; w -= 1;
        if (w >= 3) { c = p / 2 + 1; x = 2; p = 2; w -= 3; }
        else if (w == 2) { c = p / 2 + 1; a = 2; b = 0; break; }
        else if (w == 1) { x = 2; w = p / 2 + 1; p = 2; }
        else { a = p + 5; b = 0; break; }
      } else { p = 2 * c + p + 6; c = -1; x = 2; w -= 1; }
    }
  }
  norm();
  return 1;
}
int main(int argc, char **argv) {
  unsigned long long max = strtoull(argv[1], 0, 10);
  ll dump = argc > 3 && !strcmp(argv[2], "dump") ? atoll(argv[3]) : 0;
  unsigned long long nodd = 0, noddfree = 0;
  while (ops < max) {
    if (dump && (ll)visits < dump) printf("%lld %lld %lld\n", c, a, b);
    if (dump && (ll)visits >= dump) return 0;
    if (!step()) { printf("HALT at visit %llu (ops %llu): T(none, 1, %lld)\n", visits, ops, b); return 0; }
    visits++;
    if ((a & 1) && b == 0) {
      nodd++; if (c < 0) noddfree++;
      if (!dump && c < 0) printf("odd event %llu: visit %llu ops %llu  T(none, %lld, 0)\n", nodd, visits, ops, a);
      if (!dump && c >= 0) printf("odd event %llu: visit %llu ops %llu  T(%lld, %lld, 0)\n", nodd, visits, ops, c, a);
    }
  }
  if (!dump) printf("no halt: %llu visits, %llu operations, %llu odd events (%llu without bracket); now T(%lld, %lld, %lld), a/2+b = %lld\n",
         visits, ops, nodd, noddfree, c, a, b, a / 2 + b);
  return 0;
}
