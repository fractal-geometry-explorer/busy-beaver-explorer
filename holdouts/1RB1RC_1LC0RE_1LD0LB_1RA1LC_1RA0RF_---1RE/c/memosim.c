/* memosim: exact visit-level simulation of a machine of the family 1RB1RC_1LC0RE_1LD0LB_1RA1LC_????_????, with a memo
 * table on the cells next to the block.
 *
 * A visit is a step at which the head extends the tape to the left in state D; the tape is then 0^inf D>0 1^n R.
 * The sweep that follows crosses the block (D0 -> 1RA, then A> 11 -> 01 A>), works in R, and comes home in state D
 * over 1 (01)^(n/2) (the next visit, n + 2), or in state C (an *event*), or the machine halts.  What happens in R does
 * not depend on n, so the program keeps a window of W block cells and R, and counts the steps in the rest of the block
 * by formula: a visit with block n costs 1 + 2(n - W) + (steps in the window) + (n - W) + 2.
 *
 * Memo: at a visit, the first P cells of R are looked up.  As long as the head stays inside those cells (and the
 * block), what happens depends on them alone; the table gives, for a content of the P cells, the number of visits
 * until the head first steps out of them to the right, their content at that moment, the state of the head, and the
 * steps made in the window.  Entries are made from the cell-by-cell run itself, so the run is the same with any P
 * (and with P = 0, no table): the event's visit number, the window and the step count must not depend on P.
 *
 *   memosim MACHINE T0 MAXVISITS P          the true run to visit T0, then the window run
 *   memosim MACHINE T0 N check              the window run compared with the true run at each of N visits after T0
 *                                           (n, R and the step count)
 * Build: gcc -O2 -o memosim memosim.c
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define W 8
#define CAP (1 << 24)
typedef unsigned __int128 u128;
static int Wr[6][2], Dr[6][2], Sr[6][2];
static unsigned char tp[CAP]; static long long head, lo, hi; static int st; static unsigned long long tsteps;
static unsigned char win[1 << 22]; static long wlen;
static int true_to_visit(long long target, long long *vc) {
  while (*vc < target) { int y = tp[head]; int ns = Sr[st][y]; if (ns < 0) return 0;
    tp[head] = Wr[st][y]; head += Dr[st][y]; st = ns; tsteps++;
    if (head > hi) hi = head; if (head < lo) { lo = head; if (st == 3) (*vc)++; } }
  return 1; }
typedef struct { uint64_t key, val, dsteps; uint32_t dv; uint8_t s, used; } ent;
static ent *tab; static uint64_t TS, nent = 0;
static inline uint64_t hsh(uint64_t x) { x ^= x >> 33; x *= 0xff51afd7ed558ccdULL; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL; x ^= x >> 33; return x; }
static void pr128(u128 x) { char b[50]; int i = 49; b[i] = 0; if (!x) b[--i] = '0'; while (x) { b[--i] = '0' + (int)(x % 10); x /= 10; } fputs(b + i, stdout); }
/* the steps outside the window of dv consecutive visits, the first with block n */
static u128 sea(u128 n, u128 dv) { return dv * (3 * (n - W) + 3) + 3 * dv * (dv - 1); }
static void put(uint64_t key, uint64_t val, uint32_t dv, uint64_t ds, int s) {
  uint64_t idx = hsh(key) & (TS - 1);
  for (int pr = 0; pr < 8; pr++) { ent *e = &tab[(idx + pr) & (TS - 1)]; if (!e->used) { e->used = 1; e->key = key; e->val = val; e->dv = dv; e->dsteps = ds; e->s = s; nent++; return; } }
}
int main(int argc, char **argv) {
  if (argc < 5) { fprintf(stderr, "usage: memosim MACHINE T0 MAXVISITS P | memosim MACHINE T0 N check\n"); return 1; }
  const char *m = argv[1];
  for (int i = 0; i < 6; i++) for (int b = 0; b < 2; b++) { const char *t = m + 7 * i + 3 * b;
    if (t[0] == '-') Sr[i][b] = -1; else { Wr[i][b] = t[0] - '0'; Dr[i][b] = t[1] == 'R' ? 1 : -1; Sr[i][b] = t[2] - 'A'; } }
  long long T0 = atoll(argv[2]); unsigned long long MAXV = strtoull(argv[3], 0, 10); int check = !strcmp(argv[4], "check");
  int P = check ? 0 : atoi(argv[4]); int PREF = W + P; if (PREF > 64) { printf("P too large (at most %d)\n", 64 - W); return 1; }
  int LB = P / 2 + 2; if (LB > 26) LB = 26; if (LB < 4) LB = 4; TS = 1ULL << LB; tab = calloc(TS, sizeof(ent));
  head = lo = hi = CAP / 2; st = 0; long long vc = 0;
  if (!true_to_visit(T0, &vc)) { printf("the true run halts before visit %lld\n", T0); return 0; }
  unsigned long long v = T0; u128 n = 0; u128 steps = tsteps;
  { long long q = lo + 1; while (tp[q]) { q++; n++; } if (n < W) { printf("block shorter than %d cells at visit T0\n", W); return 1; }
    wlen = W + (hi - q + 1); for (long i = 0; i < W; i++) win[i] = 1; for (long long i = q; i <= hi; i++) win[W + i - q] = tp[i]; }
  long rlen = wlen - W;
  printf("start: visit %llu at step %llu, block %llu, R %ld cells; memo on the first %d cells of R\n", v, tsteps, (unsigned long long)n, rlen, P);
  long maxh = 0, pad = wlen + 64; unsigned long long nextp = 1; while (nextp <= v) nextp *= 2; unsigned long long vend = v + MAXV;
  long h = 0; int s = 0; int pending = 0; uint64_t pkey = 0, psteps = 0; unsigned long long pv = 0, hits = 0; uint64_t wsteps = 0; /* window steps since `pending` began */
  long long bad = 0;
  for (;;) {
    if (h == 0 && s == 0) {                       /* at a visit */
      if (check) {
        if (v > (unsigned long long)T0) { if (!true_to_visit(v, &vc)) { printf("the true run halts\n"); return 0; }
          long long q = lo + 1; unsigned long long nn = 0; while (tp[q]) { q++; nn++; }
          int ok = (nn == (unsigned long long)n) && (hi - q + 1 <= rlen + 60) && (u128)tsteps == steps;
          for (long long i = q; ok && i <= hi; i++) if (win[W + i - q] != tp[i]) ok = 0;
          for (long i = hi - q + 1; ok && i < rlen + 60; i++) if (win[W + i]) ok = 0;
          if (!ok) { bad++; if (bad < 4) printf("mismatch at visit %llu (true step %llu, block %llu)\n", v, tsteps, nn); } }
        if (v >= vend) { printf("%llu visits after %lld compared with the true run (block, R, step count): %lld mismatches\n", MAXV, T0, bad); return bad != 0; }
      }
      if (v >= nextp) { printf("visit %llu: step ", v); pr128(steps); printf(", deepest cell reached %ld of %ld; table %llu entries, %llu hits\n", maxh - W, rlen, (unsigned long long)nent, hits); fflush(stdout); while (nextp <= v) nextp *= 2; }
      if (!check && v >= vend) { uint64_t hh = 1469598103934665603ULL; for (long i = 0; i < wlen; i++) hh = (hh ^ win[i]) * 1099511628211ULL;
        printf("no event in %llu visits; at visit %llu: step ", MAXV, v); pr128(steps); printf(", block "); pr128(n); printf(", window hash %016llx\n", (unsigned long long)hh); return 0; }
      if (P > 0 && !check) {
        uint64_t key = 0; for (int i = 0; i < PREF; i++) key |= (uint64_t)win[i] << i;
        uint64_t idx = hsh(key) & (TS - 1); int found = 0;
        for (int pr = 0; pr < 8; pr++) { ent *e = &tab[(idx + pr) & (TS - 1)]; if (!e->used) break;
          if (e->key == key) { found = 1;
            if (v + e->dv < vend) { found = 2;
              if (pending) put(pkey, e->val, (uint32_t)(v - pv) + e->dv, wsteps - psteps + e->dsteps, e->s);
              for (int i = 0; i < PREF; i++) win[i] = (e->val >> i) & 1;
              steps += sea(n, e->dv) + e->dsteps;
              v += e->dv; n += 2 * (u128)e->dv; wsteps += e->dsteps; h = PREF; s = e->s; hits++; if (PREF > maxh) maxh = PREF;
              /* one more sweep is under way (the head is at the edge of the memo cells): its outward part */
              steps += 1 + 2 * (n - W); }
            break; } }
        if (found) { pending = 0; if (found == 2) continue; }
        else if (!pending) { pending = 1; pkey = key; pv = v; psteps = wsteps; }
      }
      steps += 1 + 2 * (n - W);                    /* D0 -> 1RA and the block outside the window, rightwards */
    }
    int y = win[h], ns = Sr[s][y];
    if (ns < 0) { printf("HALT during the sweep after visit %llu (block ", v); pr128(n); printf("), at step "); pr128(steps + 1);
      printf(", head at cell %ld of R, state %c\nwindow: ", h - W, 'A' + s); for (long i = 0; i < wlen + 8; i++) putchar('0' + win[i]); printf("\n"); return 0; }
    win[h] = Wr[s][y]; h += Dr[s][y]; s = ns; steps++; wsteps++;
    if (h > maxh) { maxh = h; if (h >= pad) { printf("the head ran off the window at visit %llu\n", v); return 0; } }
    if (h == PREF && pending && Dr[0][0] == 1 && P > 0) {     /* the head just left the memo cells to the right */
      uint64_t val = 0; for (int i = 0; i < PREF; i++) val |= (uint64_t)win[i] << i;
      put(pkey, val, (uint32_t)(v - pv), wsteps - psteps, s); pending = 0; }
    if (h < 0) {
      if (s != 3) { printf("EVENT: the head leaves the window to the left in state %c during the sweep after visit %llu, block ", 'A' + s, v); pr128(n);
        printf(", at step "); pr128(steps); printf(" (steps up to that exit)\nwindow: "); long e = wlen + 60; while (e > 0 && !win[e - 1]) e--; for (long i = 0; i < e; i++) putchar('0' + win[i]); printf("\n"); return 0; }
      steps += (n - W) + 2;                          /* home over the block, then D1 -> 1LC, C0 -> 1LD */
      v++; n += 2; h = 0; s = 0;
    }
  }
}
