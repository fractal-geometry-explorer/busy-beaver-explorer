// orbit.c: iterate the E-pass map of 1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC--- for K passes from blank tape,
// fast, by divide and conquer on the low bits of n (the 2-adic method used for Collatz parity vectors).
//
// The map: an E-event is (c, n) = `c E> 1^n` (blank beyond); the next one is (c', (3n + d)/2) where c' depends on
// c and the bit b = ceil(n/2) mod 2, and d on c and n mod 4.  Those two tables are computed here for each context
// the orbit meets, by direct simulation of the machine from `c E> 1^n` for two values of n in each class (they must
// agree), exactly like py/emap.py; py/cmap.py derives the same tables from the local rules (Lean: lean/Ctx.lean).
//
// k passes need n only mod 2^(k+1): with n_k = (3^k n + B_k) / 2^k, B_k depends on n mod 2^(k+1) only.  solve(c, X, k)
// returns (c_k, B_k) for X = n mod 2^(k+1), splitting k in halves; the leaves (k <= 40) run on machine words.  The
// cost is O(M(K) log K) instead of O(K^2) for plain big-integer iteration, so 2^30 passes take minutes.
//
// usage: orbit LOG2K [check]    K = 2^LOG2K passes from (c, n) = ("1", 19)
//   prints the context statistics, any halt, and (with "check") n_K mod 2^64 and its bit length, for comparison with
//   plain iteration (py/orbit_check.py).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include "mini_gmp_decl.h"

static const char *MACH = "1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---";
static int nx[6][2], wr[6][2], mv[6][2];

// ---- one E-pass by direct simulation ----
#define TS 8192
static unsigned char T[TS];
// run from `ctx E> 1^n`; return 0 and the next context in out, n' in *n2; or 1 for a halt
static int epass(const char *ctx, long n, char *out, long *n2) {
  memset(T, 0, TS);
  long h = TS / 2, L = strlen(ctx), lo, hi;
  for (long i = 0; i < L; i++) T[h - L + i] = ctx[i] - '0';
  for (long i = 0; i < n; i++) T[h + i] = 1;
  lo = h - L; hi = h + n;
  int st = 4, p1 = -1, p2 = -1;
  for (long k = 1; k < 100000000; k++) {
    int b = T[h], s = nx[st][b];
    if (s < 0) return 1;
    T[h] = wr[st][b]; h += mv[st][b]; p2 = p1; p1 = st * 2 + b; st = s;
    if (h < lo) lo = h;
    if (h > hi) hi = h;
    if (h <= 2 || h >= TS - 2) { fprintf(stderr, "tape overflow %s\n", ctx); exit(2); }
    if (st == 4 && T[h] && p1 == 7 && p2 != 9) {
      long r = h; while (r <= hi && T[r]) r++;
      long q = r; while (q <= hi && !T[q]) q++;
      if (q > hi && r - h > n) {   // (the odd E-pass makes a short run 11 at the end first)
        long a = lo; while (a < h && !T[a]) a++;
        long m = 0; for (long i = a; i < h; i++) out[m++] = '0' + T[i];
        out[m] = 0; *n2 = r - h; return 0;
      }
    }
  }
  fprintf(stderr, "no event %s\n", ctx); exit(2);
}

// ---- context table ----
#define MAXC 200000
#define CL 120
static char ctxs[MAXC][CL];
static int nctx = 0, nxtc[MAXC][2];   // next context per bit, -1 = halt, -2 = not computed
static int del[MAXC][4];
static unsigned long long cnt[MAXC];
#define HS (1 << 19)
static int htab[HS];
static unsigned hsh(const char *s) { unsigned h = 2166136261u; while (*s) h = (h ^ (unsigned char)*s++) * 16777619u; return h & (HS - 1); }
static int cid(const char *s) {
  unsigned h = hsh(s);
  while (htab[h]) { if (!strcmp(ctxs[htab[h] - 1], s)) return htab[h] - 1; h = (h + 1) & (HS - 1); }
  if (nctx >= MAXC || strlen(s) >= CL) { fprintf(stderr, "context table full or context too long: %s\n", s); exit(2); }
  strcpy(ctxs[nctx], s); nxtc[nctx][0] = nxtc[nctx][1] = -2; htab[h] = nctx + 1;
  return nctx++;
}
static void fill(int c) {
  char o1[CL + 64], o2[CL + 64]; long m1, m2;
  int nb[2] = {-3, -3};
  for (int r = 0; r < 4; r++) {
    int b = (r == 1 || r == 2);
    long n1 = 40 + r + 4 * strlen(ctxs[c]), n2 = n1 + 40;
    int h1 = epass(ctxs[c], n1, o1, &m1), h2 = epass(ctxs[c], n2, o2, &m2);
    if (h1 != h2) { fprintf(stderr, "inconsistent halt %s %d\n", ctxs[c], r); exit(2); }
    int id;
    if (h1) { id = -1; del[c][r] = 0; }
    else {
      long d1 = 2 * m1 - 3 * n1, d2 = 2 * m2 - 3 * n2;
      if (strcmp(o1, o2) || d1 != d2) { fprintf(stderr, "inconsistent rule %s %d\n", ctxs[c], r); exit(2); }
      id = cid(o1); del[c][r] = (int)d1;
    }
    if (nb[b] != -3 && nb[b] != id) { fprintf(stderr, "c' depends on more than b: %s\n", ctxs[c]); exit(2); }
    nb[b] = id;
  }
  nxtc[c][0] = nb[0]; nxtc[c][1] = nb[1];
}

// ---- the recursion ----
static long long passes_done = 0;   // passes completed before the current leaf
static long long halt_at = -1;      // pass index (0-based) at which a halting rule applies
static int halt_ctx = -1, halt_r = -1;
static mpz_t P3[64];                // P3[j] = 3^(2^j) cached; other powers computed
static int maxlen = 0;

static void pow3(mpz_t r, unsigned long e) { mpz_ui_pow_ui(r, 3, e); }

// leaf: k <= 40 passes, x = n mod 2^(k+1) < 2^41; returns c_k and B_k (< 2^127)
static int leaf(int c, uint64_t x, int k, unsigned __int128 *B) {
  unsigned __int128 b = 0;
  int bits = k + 1;
  for (int i = 0; i < k; i++) {
    if (nxtc[c][0] == -2) fill(c);
    int r = x & 3, bit = (r == 1 || r == 2);
    cnt[c]++;
    int c2 = nxtc[c][bit];
    if (c2 == -1) { halt_at = passes_done + i; halt_ctx = c; halt_r = r; return -1; }
    int d = del[c][r];
    b = 3 * b + ((unsigned __int128)d << i);
    x = (3 * x + d) >> 1; bits--;
    x &= (bits >= 64) ? ~0ULL : ((1ULL << bits) - 1);
    c = c2;
    int l = strlen(ctxs[c]); if (l > maxlen) maxlen = l;
  }
  passes_done += k;
  *B = b;
  return c;
}

static void set_u128(mpz_t z, unsigned __int128 v) {
  mpz_set_ui(z, (unsigned long)(v >> 64)); mpz_mul_2exp(z, z, 64); mpz_add_ui(z, z, (unsigned long)v);
}

// X = n mod 2^(k+1) (X may have more bits; they are ignored); B gets B_k; returns c_k or -1 on a halt
static int solve(int c, mpz_t X, long k, mpz_t B, int needB) {
  if (k <= 40) {
    uint64_t x = mpz_getlimbn(X, 0) & ((1ULL << (k + 1)) - 1);
    unsigned __int128 b;
    int r = leaf(c, x, (int)k, &b);
    if (r >= 0 && needB) set_u128(B, b);
    return r;
  }
  long h = k / 2;
  mpz_t B1, X1, t;
  mpz_init(B1); mpz_init(X1); mpz_init(t);
  mpz_fdiv_r_2exp(X1, X, h + 1);
  int c1 = solve(c, X1, h, B1, 1);
  if (c1 < 0) { mpz_clear(B1); mpz_clear(X1); mpz_clear(t); return -1; }
  // X1 = ((3^h X + B1) >> h) mod 2^(k-h+1)
  mpz_fdiv_r_2exp(X1, X, k + 1);
  pow3(t, h);
  mpz_mul(X1, X1, t);
  mpz_add(X1, X1, B1);
  mpz_fdiv_q_2exp(X1, X1, h);
  mpz_fdiv_r_2exp(X1, X1, k - h + 1);
  mpz_t B2; mpz_init(B2);
  int c2 = solve(c1, X1, k - h, B2, needB);
  if (c2 >= 0 && needB) {
    // B = 3^(k-h) B1 + 2^h B2
    pow3(t, k - h);
    mpz_mul(B, B1, t);
    mpz_mul_2exp(B2, B2, h);
    mpz_add(B, B, B2);
  }
  mpz_clear(B1); mpz_clear(X1); mpz_clear(t); mpz_clear(B2);
  return c2;
}

static int cmpcnt(const void *a, const void *b) {
  unsigned long long x = cnt[*(const int *)a], y = cnt[*(const int *)b];
  return x < y ? 1 : x > y ? -1 : 0;
}

int main(int argc, char **argv) {
  for (int s = 0; s < 6; s++) for (int b = 0; b < 2; b++) {
    const char *t = MACH + s * 7 + b * 3;
    if (t[2] == '-') { nx[s][b] = -1; continue; }
    wr[s][b] = t[0] - '0'; mv[s][b] = t[1] == 'R' ? 1 : -1; nx[s][b] = t[2] - 'A';
  }
  int lg = atoi(argv[1]);
  int check = argc > 2 && !strcmp(argv[2], "check");
  long K = 1L << lg;
  clock_t t0 = clock();
  mpz_t X, B; mpz_init(X); mpz_init(B);
  mpz_set_ui(X, 19);
  int c0 = cid("1");
  int c = solve(c0, X, K, B, check);
  double sec = (double)(clock() - t0) / CLOCKS_PER_SEC;
  if (c < 0) {
    printf("HALT at pass %lld (0-based) in context %s with n = %d mod 4\n", halt_at, ctxs[halt_ctx], halt_r);
  } else {
    printf("passes %ld (2^%d) from (1, 19): no halt; final context %s\n", K, lg, ctxs[c]);
  }
  printf("context table entries %d, longest context used %d cells; %.1f s\n", nctx, maxlen, sec);
  int used = 0; static int ord[MAXC];
  for (int i = 0; i < nctx; i++) if (cnt[i]) ord[used++] = i;
  qsort(ord, used, sizeof(int), cmpcnt);
  printf("contexts used %d:", used);
  for (int i = 0; i < used; i++) printf(" %s:%llu", ctxs[ord[i]], cnt[ord[i]]);
  printf("\n");
  if (check && c >= 0) {
    // n_K = (3^K * 19 + B) / 2^K
    mpz_t t; mpz_init(t); pow3(t, K); mpz_mul_ui(t, t, 19); mpz_add(t, t, B);
    mpz_t r; mpz_init(r); mpz_fdiv_r_2exp(r, t, K);
    if (mpz_sizeinbase(r, 2) > 1 || mpz_getlimbn(r, 0)) { printf("ERROR: not divisible\n"); return 3; }
    mpz_fdiv_q_2exp(t, t, K);
    printf("n_K bits %zu, n_K mod 2^64 = %lu\n", mpz_sizeinbase(t, 2), (unsigned long)mpz_getlimbn(t, 0));
  }
  return 0;
}
