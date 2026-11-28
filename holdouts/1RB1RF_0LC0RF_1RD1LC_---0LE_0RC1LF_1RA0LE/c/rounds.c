/* rounds.c: the wiki's rules B(x, y) -> B(x', y') of 1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE iterated one rule
 * at a time, with exact machine step counts (256-bit), from B(1, 0) at step 8.
 *
 *   B(x, y) := 0^inf 1^(2x) F> 1^y 0^inf
 *
 * The rules and step counts are op / op_steps of py/rules.py (checked there against the machine and the Lean map).
 *
 *   ./rounds RULES [CKPT_EVERY] [STATEFILE]      run RULES rule applications (resumes from STATEFILE if present)
 *
 * Output: a line per new record of small |d| (d = y - (2x + 1), y odd, x >= 16), the count of rules landing at each
 * d in [-16, 16] (y odd, x >= 16), and checkpoints. Halting is d = 0 with y odd.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
typedef unsigned __int128 u128;
typedef struct { u128 lo, hi; } u256;
static inline void add(u256 *s, u128 v) { u128 o = s->lo; s->lo += v; s->hi += (s->lo < o); }
static char *u128s(u128 v, char *buf) { char t[64]; int i = 0; if (!v) t[i++] = '0'; while (v) { t[i++] = '0' + (int)(v % 10); v /= 10; }
  for (int j = 0; j < i; j++) { buf[j] = t[i - 1 - j]; }
  buf[i] = 0; return buf; }
static char *u256s(u256 v, char *buf) {  /* decimal of hi*2^128+lo */
  uint32_t w[8]; for (int i = 0; i < 4; i++) { w[i] = (uint32_t)(v.lo >> (32 * i)); w[4 + i] = (uint32_t)(v.hi >> (32 * i)); }
  char t[100]; int n = 0; int nz = 1;
  while (nz) { uint64_t r = 0; nz = 0; for (int i = 7; i >= 0; i--) { uint64_t c = (r << 32) | w[i]; w[i] = (uint32_t)(c / 10); r = c % 10; if (w[i]) nz = 1; } t[n++] = '0' + (int)r; }
  for (int j = 0; j < n; j++) { buf[j] = t[n - 1 - j]; }
  buf[n] = 0; return buf; }
static double u256d(u256 v) { return (double)v.hi * 3.402823669209385e38 + (double)v.lo; }

typedef struct { uint64_t x, y; u128 rules; u256 steps; uint64_t cnt[33]; uint64_t best; uint64_t oddrules; double sum1x; } St;

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: rounds RULES [CKPT_EVERY] [STATEFILE]\n"); return 2; }
  u128 N = 0; for (char *p = argv[1]; *p; p++) N = N * 10 + (*p - '0');
  u128 CK = argc > 2 ? (u128)strtoull(argv[2], 0, 10) : (u128)1000000000;
  const char *sf = argc > 3 ? argv[3] : 0;
  St s; memset(&s, 0, sizeof s); s.x = 1; s.y = 0; s.steps.lo = 8; s.best = UINT64_MAX;
  if (sf) { FILE *f = fopen(sf, "rb"); if (f) { if (fread(&s, sizeof s, 1, f) != 1) { fprintf(stderr, "bad state\n"); return 2; } fclose(f); fprintf(stderr, "resumed\n"); } }
  char a[100], b[100];
  clock_t t0 = clock();
  uint64_t x = s.x, y = s.y; u128 r = s.rules; u256 st = s.steps;
  u128 nextck = (r / CK + 1) * CK;
  while (r < N) {
    u128 inc; uint64_t nx, ny;
    if (!(y & 1)) {
      uint64_t h = y >> 1;
      if (x >= h) { inc = 4 * (u128)x * h - 2 * (u128)h * h + 2 * (u128)x + 16 * (u128)h + 12; nx = 2 * h + 2; ny = 2 * x - 2 * h; }
      else if (x + 1 < h) { inc = 2 * (u128)x * x + 10 * (u128)x + 9; nx = 2 * x + 2; ny = 2 * h - 2 * x - 3; }
      else { inc = 2 * (u128)x * x + 10 * (u128)x + 7; nx = 2 * x + 1; ny = 0; }
    } else {
      uint64_t h = y >> 1;
      if (x > h + 1) { inc = 4 * (u128)x * h - 2 * (u128)h * h + 6 * (u128)x + 12 * (u128)h + 22; nx = 2 * h + 4; ny = 2 * x - 2 * h - 4; }
      else if (x == h + 1) { inc = 2 * (u128)x * x + 14 * (u128)x + 7; nx = 2; ny = 4 * x - 2; }
      else if (x < h) { inc = 2 * (u128)x * x + 10 * (u128)x + 9; nx = 2 * x + 2; ny = 2 * h - 2 * x - 2; }
      else { add(&st, 2 * (u128)x * x + 10 * (u128)x + 4);
        printf("HALT at rule %s step %s from B(%llu, %llu)\n", u128s(r, a), u256s(st, b), (unsigned long long)x, (unsigned long long)y); return 0; }
    }
    add(&st, inc); x = nx; y = ny; r++;
    if ((y & 1) && x >= 16) {
      int64_t d = (int64_t)y - (int64_t)(2 * x + 1);
      s.oddrules++; s.sum1x += 1.0 / (double)x;
      if (d >= -16 && d <= 16) s.cnt[d + 16]++;
      uint64_t ad = d < 0 ? -d : d;
      if (ad <= 64 && ad <= s.best) { s.best = ad < s.best ? ad : s.best;
        printf("near rule %s step %s B(%llu, %llu) d %lld\n", u128s(r, a), u256s(st, b), (unsigned long long)x, (unsigned long long)y, (long long)d); fflush(stdout); }
      if (x > (1ull << 61)) { printf("variables near 2^62, stop\n"); break; }
    }
    if (r == nextck) {
      nextck += CK;
      s.x = x; s.y = y; s.rules = r; s.steps = st;
      printf("cp %.0fs rules %s steps %s (1e%.3f) B(%llu, %llu)\n", (double)(clock() - t0) / CLOCKS_PER_SEC, u128s(r, a), u256s(st, b),
             __builtin_log10(u256d(st)), (unsigned long long)x, (unsigned long long)y); fflush(stdout);
      if (sf) { char tmp[512]; snprintf(tmp, sizeof tmp, "%s.tmp", sf); FILE *f = fopen(tmp, "wb"); fwrite(&s, sizeof s, 1, f); fclose(f); rename(tmp, sf); }
    }
  }
  s.x = x; s.y = y; s.rules = r; s.steps = st;
  printf("end rules %s steps %s (1e%.3f) B(%llu, %llu)\n", u128s(r, a), u256s(st, b), __builtin_log10(u256d(st)), (unsigned long long)x, (unsigned long long)y);
  printf("rules landing on y odd, x >= 16: %llu, sum 1/x %.4f; by d = y - (2x + 1):", (unsigned long long)s.oddrules, s.sum1x);
  for (int i = 0; i < 33; i++) { printf(" %d:%llu", i - 16, (unsigned long long)s.cnt[i]); }
  printf("\n");
  if (sf) { FILE *f = fopen(sf, "wb"); fwrite(&s, sizeof s, 1, f); fclose(f); }
  return 0;
}
