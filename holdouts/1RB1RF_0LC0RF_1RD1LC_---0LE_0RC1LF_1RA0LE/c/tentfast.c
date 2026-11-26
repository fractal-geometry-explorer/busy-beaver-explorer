/* tentfast.c: the rules B(x, y) -> B(x', y') of 1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE (c/rounds.c), K rules at a
 * time from a table (`py/gen_tab.py`), with exact machine step counts (256-bit).
 *
 *   ./tentfast TAB RULES CKPT_EVERY STATEFILE [X Y RULES0 STEPS0]
 *
 * With d = 2x - y a rule is a fold (d > 0) or a double (d < 0), and the rules at |d| <= 4 are special (the halt is
 * d = -1, y odd).  A table entry is a word of K folds and doubles with |d| >= 24 at every one of them: the composed
 * affine map, twice the steps as a quadratic in (x, y), and two linear conditions that imply all K (for
 * 2x + y >= N0; gen_tab.py checks that exactly).  The table is indexed by the parity of y and the first K binary
 * digits of 2x / (2x + y), computed in floating point: a wrong index only fails the two conditions, which are
 * exact, and then the rule is taken singly, by the code of rounds.c.  So every state with |d| < 24 is met singly,
 * the halt cannot be skipped, and the count of rules landing at each d' = y - (2x + 1) in [-16, 16] is complete.
 *
 * Checkpoints fall on exact multiples of CKPT_EVERY rules, so they can be compared with those of rounds.c.
 * STATEFILE is text: x y rules steps cnt[33]; the optional arguments give the start when it does not exist.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
typedef unsigned __int128 u128; typedef __int128 i128;
typedef struct { u128 lo, hi; } u256;
static inline void add(u256 *s, u128 v) { u128 o = s->lo; s->lo += v; s->hi += (s->lo < o); }
static inline void add256(u256 *s, u256 v) { u128 o = s->lo; s->lo += v.lo; s->hi += v.hi + (s->lo < o); }
static inline void sub256(u256 *s, u256 v) { u128 o = s->lo; s->lo -= v.lo; s->hi -= v.hi + (s->lo > o); }
static inline void addmul(u256 *p, u128 a, int64_t c) {   /* p += a * c mod 2^256, no branch on the sign of c */
  uint64_t m = (uint64_t)c; u128 l = (u128)(uint64_t)a * m, h = (u128)(uint64_t)(a >> 64) * m;
  u256 v; v.lo = l + (h << 64); v.hi = (h >> 64) + (v.lo < l);
  u128 neg = (u128)0 - (u128)(c < 0);          /* a * c = a * (uint64)c - a * 2^64 when c < 0 */
  u256 w; w.lo = (a << 64) & neg; w.hi = (a >> 64) & neg;
  add256(p, v); sub256(p, w); }
static char *u128s(u128 v, char *buf) { char t[64]; int i = 0; if (!v) t[i++] = '0'; while (v) { t[i++] = '0' + (int)(v % 10); v /= 10; }
  for (int j = 0; j < i; j++) { buf[j] = t[i - 1 - j]; }
  buf[i] = 0; return buf; }
static char *u256s(u256 v, char *buf) {
  uint32_t w[8]; for (int i = 0; i < 4; i++) { w[i] = (uint32_t)(v.lo >> (32 * i)); w[4 + i] = (uint32_t)(v.hi >> (32 * i)); }
  char t[100]; int n = 0; int nz = 1;
  while (nz) { uint64_t r = 0; nz = 0; for (int i = 7; i >= 0; i--) { uint64_t c = (r << 32) | w[i]; w[i] = (uint32_t)(c / 10); r = c % 10; if (w[i]) nz = 1; } t[n++] = '0' + (int)r; }
  for (int j = 0; j < n; j++) { buf[j] = t[n - 1 - j]; }
  buf[n] = 0; return buf; }
static u256 s256(const char *p) { u256 v = {0, 0};
  for (; *p >= '0' && *p <= '9'; p++) { /* v = v * 10 + digit */
    u256 a = v; for (int i = 0; i < 9; i++) add256(&v, a);
    add(&v, (u128)(*p - '0')); }
  return v; }
static u128 s128(const char *p) { u128 v = 0; for (; *p >= '0' && *p <= '9'; p++) v = v * 10 + (*p - '0'); return v; }
static double u256d(u256 v) { return (double)v.hi * 3.402823669209385e38 + (double)v.lo; }

typedef struct { int64_t ok, a[6], c1[3], c2[3], q[6]; } Ent;

int main(int argc, char **argv) {
  if (argc < 5) { fprintf(stderr, "usage: tentfast TAB RULES CKPT_EVERY STATEFILE [X Y RULES0 STEPS0]\n"); return 2; }
  FILE *f = fopen(argv[1], "rb"); if (!f) { perror(argv[1]); return 2; }
  int64_t hd[4]; if (fread(hd, 8, 4, f) != 4) return 2;
  int K = (int)hd[0]; uint64_t N0 = 1ull << hd[1]; int64_t M = hd[2];
  size_t ne = (size_t)2 << K; Ent *tab = malloc(ne * sizeof(Ent));
  if (fread(tab, sizeof(Ent), ne, f) != ne) { fprintf(stderr, "short table\n"); return 2; }
  fclose(f);
  u128 N = s128(argv[2]), CK = s128(argv[3]); const char *sf = argv[4];
  uint64_t x = 1, y = 0, cnt[33]; u128 r = 0; u256 st = {8, 0}; memset(cnt, 0, sizeof cnt);
  char a[100], b[100], line[4096];
  f = fopen(sf, "r");
  if (f) { if (!fgets(line, sizeof line, f)) return 2; fclose(f);
    char *p = line, *e; x = strtoull(p, &e, 10); p = e; y = strtoull(p, &e, 10); p = e; while (*p == ' ') p++;
    r = s128(p); while (*p > ' ') p++; while (*p == ' ') p++; st = s256(p); while (*p > ' ') p++;
    for (int i = 0; i < 33; i++) { cnt[i] = strtoull(p, &e, 10); p = e; }
    fprintf(stderr, "resumed at rule %s\n", u128s(r, a)); }
  else if (argc >= 9) { x = strtoull(argv[5], 0, 10); y = strtoull(argv[6], 0, 10); r = s128(argv[7]); st = s256(argv[8]); }
#ifdef NOSTEPS
  st.lo = 0; st.hi = 0;   /* the hunt build does not count steps: the steps field is 0 */
#endif
  struct timespec t0, t1; clock_gettime(CLOCK_MONOTONIC, &t0);
  u128 nextck = (r / CK + 1) * CK; uint64_t ntab = 0, nslow = 0;
  const double scale = (double)(1ull << K), scale3 = (double)(1ull << (3 * K)); const size_t mask = ((size_t)1 << K) - 1; uint64_t nmiss2 = 0, nmiss3 = 0;
  while (r < N) {
    int64_t d = (int64_t)(2 * x) - (int64_t)y; uint64_t n = 2 * x + y;
#ifdef NOSTEPS
#define STEPS(e)
#else
#define STEPS(e) { u128 xx = (u128)x * x, xy = (u128)x * y, yy = (u128)y * y; u256 p = {0, 0}; \
        addmul(&p, xx, (e)->q[0]); addmul(&p, xy, (e)->q[1]); addmul(&p, yy, (e)->q[2]); \
        addmul(&p, x, (e)->q[3]); addmul(&p, y, (e)->q[4]); addmul(&p, 1, (e)->q[5]); \
        p.lo = (p.lo >> 1) | (p.hi << 127); p.hi >>= 1; add256(&st, p); }
#endif
#define VALID(e) ((e)->ok && (i128)(e)->c1[0] * x + (i128)(e)->c1[1] * y + (e)->c1[2] >= 0 && (i128)(e)->c2[0] * x + (i128)(e)->c2[1] * y + (e)->c2[2] >= 0)
#define APPLY(e) { STEPS(e) \
        uint64_t nx = (uint64_t)((i128)(e)->a[0] * x + (i128)(e)->a[1] * y + (e)->a[2]); \
        uint64_t ny = (uint64_t)((i128)(e)->a[3] * x + (i128)(e)->a[4] * y + (e)->a[5]); \
        x = nx; y = ny; r += K; ntab++; }
#define TALLY if ((y & 1) && x >= 16) { int64_t dd = (int64_t)y - (int64_t)(2 * x + 1); \
      if (dd >= -16 && dd <= 16) { cnt[dd + 16]++; \
        if (dd >= -4 && dd <= 4) { printf("near rule %s step %s B(%llu, %llu) d %lld\n", u128s(r, a), u256s(st, b), (unsigned long long)x, (unsigned long long)y, (long long)dd); fflush(stdout); } } }
    if (n >= N0 && r + 3 * K <= nextck) {
      /* three table steps from one division: the K digits of each later index are the next K digits of
         2x / n, complemented when the digit before them is 1 (the tent map shifts the digits that way); the drift
         makes this a guess, and the exact conditions of each entry decide */
      uint64_t U = (uint64_t)((double)(int64_t)(2 * x) * scale3 / (double)(int64_t)n);
      size_t k1 = (U >> (2 * K)) & mask, k2 = ((U >> K) & mask) ^ ((0 - (k1 & 1)) & mask), k3 = (U & mask) ^ ((0 - ((U >> K) & 1)) & mask);
      const Ent *e1 = &tab[((size_t)(y & 1) << K) | k1];
      const Ent *e2 = &tab[((size_t)((e1->ok >> 1) & 1) << K) | k2];
      const Ent *e3 = &tab[((size_t)((e2->ok >> 1) & 1) << K) | k3];
      if (VALID(e1)) { APPLY(e1) TALLY
        if (VALID(e2)) { APPLY(e2) TALLY
          if (VALID(e3)) { APPLY(e3) goto landed; } else nmiss3++; } else nmiss2++;
        goto landed; }
    }
    if (n >= N0 && (d >= M || d <= -M) && r + K <= nextck) {
      size_t key = ((size_t)(y & 1) << K) | (size_t)((double)(int64_t)(2 * x) * scale / (double)(int64_t)n);
      const Ent *e = &tab[key];
      if (VALID(e)) { APPLY(e) goto landed; }
    }
    { u128 inc; uint64_t nx, ny, h = y >> 1; nslow++;
      if (!(y & 1)) {
        if (x >= h) { inc = 4 * (u128)x * h - 2 * (u128)h * h + 2 * (u128)x + 16 * (u128)h + 12; nx = 2 * h + 2; ny = 2 * x - 2 * h; }
        else if (x + 1 < h) { inc = 2 * (u128)x * x + 10 * (u128)x + 9; nx = 2 * x + 2; ny = 2 * h - 2 * x - 3; }
        else { inc = 2 * (u128)x * x + 10 * (u128)x + 7; nx = 2 * x + 1; ny = 0; }
      } else {
        if (x > h + 1) { inc = 4 * (u128)x * h - 2 * (u128)h * h + 6 * (u128)x + 12 * (u128)h + 22; nx = 2 * h + 4; ny = 2 * x - 2 * h - 4; }
        else if (x == h + 1) { inc = 2 * (u128)x * x + 14 * (u128)x + 7; nx = 2; ny = 4 * x - 2; }
        else if (x < h) { inc = 2 * (u128)x * x + 10 * (u128)x + 9; nx = 2 * x + 2; ny = 2 * h - 2 * x - 2; }
        else {
#ifdef NOSTEPS
          st.lo = 0; st.hi = 0;
#else
          add(&st, 2 * (u128)x * x + 10 * (u128)x + 4);
#endif
          printf("HALT at rule %s step %s from B(%llu, %llu)\n", u128s(r, a), u256s(st, b), (unsigned long long)x, (unsigned long long)y);
          f = fopen("HALT.txt", "w"); fprintf(f, "HALT at rule %s step %s from B(%llu, %llu)\n", u128s(r, a), u256s(st, b), (unsigned long long)x, (unsigned long long)y); fclose(f);
          return 0; }
      }
      add(&st, inc); x = nx; y = ny; r++; }
  landed:
    TALLY
    if (x > (1ull << 60) || y > (1ull << 60)) { printf("variables near 2^60, stop\n"); break; }
    if (r == nextck) {
#ifdef NOSTEPS
      st.lo = 0; st.hi = 0;
#endif
      nextck += CK; clock_gettime(CLOCK_MONOTONIC, &t1);
      printf("cp %.0fs rules %s steps %s (1e%.3f) B(%llu, %llu) tab %llu single %llu miss %llu %llu\n", (double)(t1.tv_sec - t0.tv_sec), u128s(r, a), u256s(st, b),
             __builtin_log10(u256d(st)), (unsigned long long)x, (unsigned long long)y, (unsigned long long)ntab, (unsigned long long)nslow, (unsigned long long)nmiss2, (unsigned long long)nmiss3); fflush(stdout);
      char tmp[512]; snprintf(tmp, sizeof tmp, "%s.tmp", sf); f = fopen(tmp, "w");
      fprintf(f, "%llu %llu %s %s", (unsigned long long)x, (unsigned long long)y, u128s(r, a), u256s(st, b));
      for (int i = 0; i < 33; i++) fprintf(f, " %llu", (unsigned long long)cnt[i]);
      fprintf(f, "\n"); fclose(f); rename(tmp, sf);
    }
  }
  printf("end rules %s steps %s B(%llu, %llu); rules landing on y odd, x >= 16, by d = y - (2x + 1):", u128s(r, a), u256s(st, b), (unsigned long long)x, (unsigned long long)y);
  for (int i = 0; i < 33; i++) printf(" %d:%llu", i - 16, (unsigned long long)cnt[i]);
  printf("\n");
  return 0;
}
