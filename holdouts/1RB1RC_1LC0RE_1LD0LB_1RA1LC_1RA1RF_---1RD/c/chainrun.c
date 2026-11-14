/* chainrun: the exact accelerated run of 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA1RF_---1RD at the level of visits, in C.
 * The same algorithm as py/chain.py (`run`): a closed-form jump over the double visits that turn inside the chain of
 * mod-4 counters, then one double visit cell by cell; visit numbers and block lengths in 128 bits, step counts in
 * 256 bits.  It stops before the double visit that ends in an event or a halt and writes the state there, so that
 * py/chain.py can replay that last double visit and print what the event leaves.
 *
 *   chainrun STATE MAXPASS OUT        STATE, OUT: files holding  visit block steps passes R  (R as 0/1 text)
 *   chainrun -direct VISIT OUT        the state file of the direct run from blank tape at that (even) visit
 *
 * Build: gcc -O2 -o chainrun chainrun.c
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 u128;
typedef unsigned long long u64;
typedef struct { u64 w[4]; } u256;
static const char *MACH = "1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA1RF_---1RD";
static int Wr[6][2], Dr[6][2], Sr[6][2];
#define SEAW 16
#define MAXR (1 << 16)
static unsigned char win[MAXR + 256], R[MAXR], Rsave[MAXR];
static int rlen;
static unsigned char S[4][12];
static const char *SW[4] = {"baabaa", "abbabb", "bbbbbb", "aaaaaa"};

static void add128(u256 *a, u128 x) {
  u64 lo = (u64)x, hi = (u64)(x >> 64); unsigned __int128 c = (u128)a->w[0] + lo; a->w[0] = (u64)c; c >>= 64;
  c += (u128)a->w[1] + hi; a->w[1] = (u64)c; c >>= 64;
  c += a->w[2]; a->w[2] = (u64)c; c >>= 64; a->w[3] += (u64)c;
}
static void addmul(u256 *a, u128 x, u128 y) {          /* a += x * y */
  u64 xl = (u64)x, xh = (u64)(x >> 64), yl = (u64)y, yh = (u64)(y >> 64);
  u128 p0 = (u128)xl * yl, p1 = (u128)xl * yh, p2 = (u128)xh * yl, p3 = (u128)xh * yh;
  u256 t = {{0, 0, 0, 0}};
  t.w[0] = (u64)p0;
  u128 c = (p0 >> 64) + (u64)p1 + (u64)p2; t.w[1] = (u64)c; c >>= 64;
  c += (p1 >> 64) + (p2 >> 64) + (u64)p3; t.w[2] = (u64)c; c >>= 64;
  t.w[3] = (u64)(c + (p3 >> 64));
  u128 k = 0;
  for (int i = 0; i < 4; i++) { k += (u128)a->w[i] + t.w[i]; a->w[i] = (u64)k; k >>= 64; }
}
static void pr256(FILE *f, u256 a) {
  char b[90]; int i = 89; b[i] = 0;
  int z = !(a.w[0] | a.w[1] | a.w[2] | a.w[3]); if (z) b[--i] = '0';
  while (a.w[0] | a.w[1] | a.w[2] | a.w[3]) { u128 r = 0; for (int j = 3; j >= 0; j--) { u128 c = (r << 64) | a.w[j]; a.w[j] = (u64)(c / 10); r = c % 10; } b[--i] = '0' + (int)r; }
  fputs(b + i, f);
}
static u256 parse256(const char *s) { u256 a = {{0, 0, 0, 0}};
  for (; *s >= '0' && *s <= '9'; s++) { u128 c = *s - '0'; for (int j = 0; j < 4; j++) { c += (u128)a.w[j] * 10; a.w[j] = (u64)c; c >>= 64; } }
  return a; }
static u128 parse128(const char *s) { u128 x = 0; for (; *s >= '0' && *s <= '9'; s++) x = x * 10 + (*s - '0'); return x; }
static void pr128(FILE *f, u128 x) { u256 a = {{(u64)x, (u64)(x >> 64), 0, 0}}; pr256(f, a); }

/* one sweep on the window (w block cells + R): 0 = next visit, 1 = event, 2 = halt; *st = steps inside the window */
static int sweep(int w, long *st, long *mh) {
  int len = w + rlen + 64; memset(win, 1, w); memcpy(win + w, R, rlen); memset(win + w + rlen, 0, 64);
  long h = 0, k = 0, m = 0; int s = 0;
  for (;;) {
    if (h < 0) break;
    if (h >= len) { fprintf(stderr, "the head ran off the window\n"); exit(2); }
    int y = win[h], ns = Sr[s][y];
    if (ns < 0) { *st = k + 1; *mh = m; return 2; }
    win[h] = Wr[s][y]; h += Dr[s][y]; s = ns; k++; if (h > m) m = h;
  }
  *st = k; *mh = m;
  if (s == 3) { for (int i = w + rlen; i < len; i++) if (win[i]) { fprintf(stderr, "R grew without an event\n"); exit(2); }
    memcpy(R, win + w, rlen); return 0; }
  if (s == 2) return 1;
  fprintf(stderr, "left exit in state %c\n", 'A' + s); exit(2);
}
static inline u128 count(int s, u128 t, int r) { int k0 = ((r - s) % 4 + 4) % 4; return t <= (u128)k0 ? 0 : 1 + (t - 1 - k0) / 4; }
static void save(const char *fn, u128 v, u128 n, u256 steps, u64 pass, const unsigned char *r) {
  FILE *o = fopen(fn, "w"); pr128(o, v); fputc(' ', o); pr128(o, n); fputc(' ', o); pr256(o, steps); fprintf(o, " %llu ", pass);
  for (int i = 0; i < rlen; i++) fputc('0' + r[i], o); fputc('\n', o); fclose(o);
}
int main(int argc, char **argv) {
  for (int i = 0; i < 6; i++) for (int b = 0; b < 2; b++) { const char *t = MACH + 7 * i + 3 * b;
    if (t[0] == '-') Sr[i][b] = -1; else { Wr[i][b] = t[0] - '0'; Dr[i][b] = t[1] == 'R' ? 1 : -1; Sr[i][b] = t[2] - 'A'; } }
  for (int i = 0; i < 4; i++) for (int j = 0; j < 6; j++) { S[i][2 * j] = SW[i][j] == 'b'; S[i][2 * j + 1] = 1; }
  if (argc == 4 && !strcmp(argv[1], "-direct")) {          /* the true run from blank tape to a visit */
    long target = atol(argv[2]); static unsigned char tp[1 << 22]; long h = 1 << 21, lo = h, hi = h, v = 0; u64 k = 0; int s = 0;
    while (v < target) { int y = tp[h]; int ns = Sr[s][y]; if (ns < 0) { printf("halt\n"); return 1; }
      tp[h] = Wr[s][y]; h += Dr[s][y]; s = ns; k++; if (h > hi) hi = h; if (h < lo) { lo = h; if (s == 3) v++; } }
    long q = lo + 1, n = 0; while (tp[q]) { q++; n++; }
    rlen = (int)(hi - q + 1); memcpy(R, tp + q, rlen);
    u256 st = {{k, 0, 0, 0}}; save(argv[3], (u128)v, (u128)n, st, 0, R);
    printf("visit %ld at step %llu: block %ld, R %d cells\n", v, k, n, rlen); return 0;
  }
  if (argc < 4) { fprintf(stderr, "usage: chainrun STATE MAXPASS OUT | chainrun -direct VISIT OUT\n"); return 1; }
  FILE *f = fopen(argv[1], "r"); static char vs[64], ns_[64], ss[128], rs[MAXR]; u64 pass0;
  if (!f || fscanf(f, "%63s %63s %127s %llu %65000s", vs, ns_, ss, &pass0, rs) != 5) { fprintf(stderr, "bad state file\n"); return 1; }
  fclose(f);
  u128 v = parse128(vs), n = parse128(ns_); u256 steps = parse256(ss); rlen = strlen(rs); for (int i = 0; i < rlen; i++) R[i] = rs[i] - '0';
  u64 maxpass = strtoull(argv[2], 0, 10), pass = pass0, every = getenv("EVERY") ? strtoull(getenv("EVERY"), 0, 10) : 1000000; long maxdep = 0;
  static int st[8192]; static u128 arr[8192];
  for (;;) {
    int m = 0;
    if (!memcmp(R, "\0\1\0\1\0\1", 6)) { int j = 6; while (j + 12 <= rlen) { int i; for (i = 0; i < 4; i++) if (!memcmp(R + j, S[i], 12)) break; if (i == 4) break; st[m++] = i; j += 12; } }
    u128 v0 = v, n0 = n; u256 steps0 = steps; memcpy(Rsave, R, rlen);
    if (m > 0) {
      u128 need = 0;
      for (int j = m - 1; j >= 0; j--) { int k0 = (4 - st[j]) % 4; need += need < (u128)k0 ? 0 : 1 + (need - k0) / 3; arr[j] = need; }
      if (need >> 120) { fprintf(stderr, "counter too large for 128 bits\n"); return 3; }
      if (need) {
        u128 K = need;
        addmul(&steps, K, 6 * n + 146); addmul(&steps, 12 * K, K - 1);
        for (int j = 0; j < m; j++) { u128 t = arr[j]; if (!t) break;
          add128(&steps, 128 * (count(st[j], t, 1) + count(st[j], t, 3))); add128(&steps, 108 * count(st[j], t, 2));
          int s2 = (int)((st[j] + t) % 4); if (s2 != st[j]) memcpy(R + 6 + 12 * j, S[s2], 12); }
        v += 2 * K; n += 4 * K;
      }
    }
    int kind = 0; long ws, mh;
    for (int t = 0; t < 2; t++) {
      int w = n < SEAW ? (int)(n - (n % 2)) : SEAW; u128 k = n - w;
      kind = sweep(w, &ws, &mh);
      if (kind) break;
      add128(&steps, 1 + 2 * k); add128(&steps, (u128)ws); add128(&steps, k + 2);
      v += 1; n += 2; if (mh - w > maxdep) maxdep = mh - w;
    }
    if (kind) {
      memcpy(R, Rsave, rlen); save(argv[3], v0, n0, steps0, pass, Rsave);
      printf("%s in the double visit after pass %llu; the state before it (visit ", kind == 2 ? "HALT" : "EVENT", pass);
      pr128(stdout, v0); printf(", before the jump) is in %s\n", argv[3]); return 0;
    }
    pass++;
    if (pass % every == 0 || pass - pass0 >= maxpass) {
      save(argv[3], v, n, steps, pass, R);
      printf("pass %llu: visit ", pass); pr128(stdout, v); printf(" step "); pr256(stdout, steps); printf(" deepest %ld of %d\n", maxdep, rlen); fflush(stdout);
      if (pass - pass0 >= maxpass) return 0;
    }
  }
}
