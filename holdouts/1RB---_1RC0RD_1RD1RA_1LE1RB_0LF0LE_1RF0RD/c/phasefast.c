/* The macro map of 1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD (`py/macro.py`, the same map as the proved `phase`
 * of `lean/Orbit.lean`), iterated far, in time about linear in the number of bits it touches.
 *
 * State at an event: the bit string X (M bits, a packed bit array with a moving low end) and j = (N + 2) / 3.
 * One phase:
 *   * events: add 2^j, 2^(j+1), ... (carry propagation) until an addition carries out of bit M - 1; what is left
 *     is R = X + 2^j - 2^M.  After an overflow the string is shorter than 2^j0, so these additions only set the
 *     5k bits between j0 and M (no long carries), which is why a phase costs O(k) and not O(M).
 *   * overflow: R even: X = R + 1, M + 1, j + 1.  R odd: k = number of low pairs whose low bit is 1 (stuck, i.e. the
 *     halting case, if 2k reaches M); X = C(r) + (R >> 2k), M + 3k + 1, j - 2k + 1 (j = 0: X >> 1, M - 1, j = 1).
 *     C(r) = sum over levels of c_t 8^(i-1) as in `macro.C`, added and subtracted in place, bit by bit.
 * After every overflow it tests the landing condition of `halts_iff_lands` (lean/Landing.lean): X = 2^j - 1 with
 * j + 1 <= M.  Either that or the stuck case would mean the machine halts; the program stops and says so.
 *
 * usage: phasefast dump K            the first K overflows: index M j X(hex, top first), to compare with macro.py
 *        phasefast dump K STRIDE     the same, X only at every STRIDE-th overflow
 *        phasefast run K [EVERY]     K overflows; a progress line every EVERY; statistics at the end
 * build: gcc -O2 -o phasefast phasefast.c
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static uint64_t *w;          /* bit i of X is bit (lo + i) of the array */
static uint64_t cap, lo, M, j; /* cap in words */

static inline int getb(uint64_t i) { uint64_t p = lo + i; return (w[p >> 6] >> (p & 63)) & 1; }
static inline void setb(uint64_t i) { uint64_t p = lo + i; w[p >> 6] |= 1ULL << (p & 63); }
static inline void clrb(uint64_t i) { uint64_t p = lo + i; w[p >> 6] &= ~(1ULL << (p & 63)); }

/* make room for bits 0 .. need-1 of X (and zeroed words above) */
static void room(uint64_t need) {
  uint64_t hiword = (lo + need) / 64 + 2;
  if (hiword <= cap) return;
  uint64_t low = lo / 64;
  if (low > cap / 2) {          /* compact: drop the words below lo */
    memmove(w, w + low, (cap - low) * 8);
    memset(w + cap - low, 0, low * 8);
    lo -= low * 64;
    if ((lo + need) / 64 + 2 <= cap) return;
  }
  uint64_t nc = cap * 2;
  while ((lo + need) / 64 + 2 > nc) nc *= 2;
  w = realloc(w, nc * 8);
  if (!w) { fprintf(stderr, "out of memory\n"); exit(2); }
  memset(w + cap, 0, (nc - cap) * 8);
  cap = nc;
}

static void add_one(uint64_t p) { while (getb(p)) clrb(p++); setb(p); }
static void sub_one(uint64_t p) { while (!getb(p)) setb(p++); clrb(p); }
static void add_small(uint64_t v, uint64_t at) { for (int b = 0; v; b++, v >>= 1) if (v & 1) add_one(at + b); }
static void sub_small(uint64_t v, uint64_t at) { for (int b = 0; v; b++, v >>= 1) if (v & 1) sub_one(at + b); }

static uint64_t *T; static uint64_t Tcap;
/* stats */
static uint64_t khist[64], keven, kmax, kmaxat, t1max, t1maxat, generic;
static double ratio_max; static uint64_t ratio_at;

/* one phase; returns 0 normally, 1 stuck (odd pairs reach the top), 2 landing, 3 N < 1 (not modelled) */
static int phase(uint64_t idx, uint64_t *kout) {
  uint64_t j0 = j;
  /* events */
  for (;;) {
    uint64_t p = j;
    while (p < M && getb(p)) { clrb(p); p++; }
    if (p >= M) break;            /* carried out: R = X + 2^j - 2^M is what is left */
    if (p != j) generic++;
    setb(p); j++;
  }
  (void)j0;
  if (!getb(0)) {                 /* R even */
    setb(0); M += 1; j += 1; room(M + 8); *kout = 0; keven++;
  } else {
    uint64_t k = 0;
    while (getb(2 * k)) { k++; if (2 * k >= M) return 1; }
    *kout = k;
    if (k < 64) khist[k]++; else khist[63]++;
    if (k > kmax) { kmax = k; kmaxat = idx; }
    if (idx > 100) { double r = 2.0 * k / M; if (r > ratio_max) { ratio_max = r; ratio_at = idx; } }
    /* T[p] = consecutive 11 pairs from pair p upward, within the k pairs */
    if (k + 1 > Tcap) { Tcap = 2 * (k + 1); T = realloc(T, Tcap * 8); }
    T[k] = 0;
    for (uint64_t p = k; p-- > 0;) T[p] = getb(2 * p + 1) ? T[p + 1] + 1 : 0;
    int top11 = getb(2 * (k - 1) + 1);
    uint64_t newM = M + 3 * k + 1;
    /* shift right by 2k: bits 0..2k-1 (r) are no longer part of X; clear them first */
    for (uint64_t b = 0; b < 2 * k; b++) clrb(b);
    lo += 2 * k;
    room(newM + 16);
    /* C(r) = base + sum_{i=2..k} term_i, term_i = c(t_i) 8^(i-1) (t_i = T[k-i]; all-11 case: 2c(i-1)+21) */
    add_small(top11 ? 104 : 43, 0);
    for (uint64_t i = 2; i <= k; i++) {
      uint64_t t = T[k - i], s = 3 * (i - 1);
      if (t == i) {               /* 2 c(i-1) + 21 */
        if (i - 1 == 0) add_small(105, s);
        else { add_small(31, s + 2 * (i - 2) + 4); sub_small(21, s); }   /* 496·4^(i-2) - 21 */
      } else if (t == 0) add_small(42, s);
      else { add_small(31, s + 2 * (t - 1) + 3); sub_small(21, s); }     /* 248·4^(t-1) - 21 */
    }
    M = newM;
    if (j + 1 < 2 * k) return 3;
    j = j - 2 * k + 1;
    if (j == 0) { clrb(0); lo += 1; M -= 1; j = 1; }
  }
  /* landing test: X = 2^j - 1 with j + 1 <= M */
  uint64_t t1 = 0;
  while (t1 < M && getb(t1)) t1++;
  if (t1 > t1max) { t1max = t1; t1maxat = idx; }
  if (t1 == j && j + 1 <= M) {
    uint64_t b = j;
    while (b < M && !getb(b)) b++;
    if (b == M) return 2;
  }
  return 0;
}

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: phasefast dump|run K [EVERY]\n"); return 1; }
  int dump = !strcmp(argv[1], "dump");
  uint64_t K = strtoull(argv[2], 0, 10), every = argc > 3 ? strtoull(argv[3], 0, 10) : (dump ? 1 : 1000000);
  /* reserve the whole array up front (M grows about 5.1 bits a phase; calloc maps zero pages lazily), so that no
   realloc has to copy gigabytes near the end of a long run */
  cap = 1024 + (uint64_t)(5.3 * (double)K / 64); w = calloc(cap, 8); lo = 0;
  if (!w) { fprintf(stderr, "out of memory\n"); return 2; }
  M = 2; j = 1;                    /* the event at step 39: X = 0, M = 2, N = 1 */
  clock_t c0 = clock();
  for (uint64_t i = 0; i < K; i++) {
    uint64_t k;
    int r = phase(i, &k);
    if (r) {
      printf("STOP at overflow %llu: %s (M=%llu j=%llu)\n", (unsigned long long)i,
             r == 1 ? "STUCK: odd pairs reach the top bit (halting case)" :
             r == 2 ? "LANDING: X = 2^j - 1 (the machine halts)" : "N < 1, not modelled",
             (unsigned long long)M, (unsigned long long)j);
      return 0;
    }
    /* invariant check: no bit at or above M */
    if (dump) {
      printf("%llu %llu %llu", (unsigned long long)i, (unsigned long long)M, (unsigned long long)j);
      if (i % every) { printf("\n"); continue; }
      printf(" ");
      uint64_t top = M; while (top > 0 && !getb(top - 1)) top--;
      if (!top) printf("0");
      for (uint64_t b = (top + 3) / 4 * 4; b > 0; b -= 4) {
        int v = 0; for (int q = 3; q >= 0; q--) v = 2 * v + (b - 4 + q < M ? getb(b - 4 + q) : 0);
        printf("%x", v);
      }
      printf("\n");
      for (uint64_t b = M; b < M + 64; b++) if (getb(b)) { printf("BIT ABOVE M at %llu\n", (unsigned long long)i); return 4; }
    } else if ((i + 1) % every == 0) {
      fprintf(stderr, "%llu overflows: M=%llu j=%llu kmax=%llu t1max=%llu  %.0fs\n", (unsigned long long)i + 1,
              (unsigned long long)M, (unsigned long long)j, (unsigned long long)kmax, (unsigned long long)t1max,
              (double)(clock() - c0) / CLOCKS_PER_SEC);
    }
  }
  if (!dump) {
    printf("overflows %llu, no stuck case, no landing\n", (unsigned long long)K);
    printf("final M %llu bits, j %llu\n", (unsigned long long)M, (unsigned long long)j);
    printf("R even %llu\n", (unsigned long long)keven);
    for (int k = 1; k < 64; k++) if (khist[k]) printf("k=%d%s %llu\n", k, k == 63 ? "+" : "", (unsigned long long)khist[k]);
    printf("max k %llu at overflow %llu; max 2k/M after overflow 100: %.6f at %llu (a halt needs 1)\n",
           (unsigned long long)kmax, (unsigned long long)kmaxat, ratio_max, (unsigned long long)ratio_at);
    printf("longest run of low ones at an output %llu at overflow %llu (landing needs exactly j ones and nothing above)\n",
           (unsigned long long)t1max, (unsigned long long)t1maxat);
    uint64_t bl = 0;
    for (uint64_t b = 0; b < M; b += 2) bl += !getb(b);
    printf("pairs of the final string whose low bit is 0 (blockers, counted from bit 0): %llu of %llu\n",
           (unsigned long long)bl, (unsigned long long)(M + 1) / 2);
    printf("event additions with a carry %llu\n", (unsigned long long)generic);
    printf("cpu %.1fs\n", (double)(clock() - c0) / CLOCKS_PER_SEC);
  }
  return 0;
}
