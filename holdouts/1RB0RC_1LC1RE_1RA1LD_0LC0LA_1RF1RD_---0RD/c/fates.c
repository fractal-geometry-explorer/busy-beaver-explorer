// fates.c: exhaustive fate of every zigzag start t(a, 0, r) (t = y or Y, a >= 3, r >= 2) with level N = a + r <= M
// under the pass map of 1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD.
// The functions jump, zstart, G and pass are copied from c/prun.c (which is checked against the Lean map).
//   ./fates M ex.bin hl.bin    ex: 0 halts, else an id of the first zigzag start above level M; hl: level of the last
//                               zigzag start before the halt.  Layout: tag y then Y; per tag levels N = 5..M; per level a = 3..N-2.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef long long I;
typedef unsigned __int128 W;
#include "fcases.h"
static const char TAG[] = "zywuZYWU";
enum { z, y, w, u, Z, Y, Wt, U };
static int lastcode;
static I jump(int *t, I v[3], W *st, int *hc) {
    I a = v[0], b = v[1], c = v[2], k;
    lastcode = 100 + ((*t == w || *t == Wt) ? 0 : (*t == u || *t == U) ? 1 : 2);
    if ((*t == w || *t == Wt) && b >= 2 && c >= 1) { k = b / 2; v[0] = a + 4 * k; v[1] = b - 2 * k; *st = (W)6 * k; return k; }
    if ((*t == u && b >= 1) || (*t == U && a >= 1 && b >= 1)) { v[1] = 0; v[2] = c + 2 * b; *st = (W)4 * b; return b; }
    if ((*t == y || *t == Y) && a >= 3 && c >= 2) {
        k = a / 3; if (c - 1 < k) k = c - 1;
        v[0] = a - 3 * k; v[1] = b + 2 * k; v[2] = c - k;
        *st = (W)k * (W)(4 * b + 9) + (W)4 * k * (k - 1); return 2 * k;
    }
    int r = fc_step(t, v, st); lastcode = r;
    if (r < 0) { *hc = -1 - r; return 0; }
    return 1;
}
static int zstart(int t, I v[3]) { return (t == y || t == Y) && v[0] >= 3 && v[2] >= 2; }
/* growth table: [Y?][e][j odd] = t', c, d, f (2 * frames constant), s0, s1, s2 (steps s0 + s1 q + s2 j + 4q^2 + 4qj) */
static const int G[2][3][2][7] = {
  { { {y, 2, 1, 8, 17, 19, 7}, {y, 5, 4, 7, 15, 19, 7} },
    { {y, 7, 4, 8, 20, 19, 7}, {y, 4, 1, 9, 22, 19, 7} },
    { {Y, 2, 1, 6, 29, 19, 7}, {Y, 5, 4, 5, 27, 19, 7} } },
  { { {y, 5, 1, 6, 17, 19, 7}, {y, 8, 4, 5, 15, 19, 7} },
    { {y, 11, 5, 14, 47, 27, 11}, {y, 8, 2, 15, 49, 27, 11} },
    { {0} , {0} } } };

/* one pass from a zigzag start if it is away from the boundary: returns frames (>0), or 0 if not applicable */
static W pass(int *t, I v[3], W *st) {
    I a = v[0], j = v[1], r = v[2], q = a / 3, e = a % 3;
    int big = *t == Y;
    if (r <= q - 1) {
        v[0] = a - 3 * r + 1; v[1] = 0; v[2] = 4 * r + 2 * j + 2;
        *st = 3 + (W)2 * j + (W)9 * r + (W)4 * j * r + (W)4 * r * r;
        return (W)j + (W)4 * r - 1;
    }
    if (r >= q + 7) {
        if (big && e == 2) {
            v[0] = 5; v[1] = j + 2 * q + 2; v[2] = r - q - 1; *t = y;
            *st = 35 + (W)13 * q + (W)4 * j + (W)4 * q * q + (W)4 * q * j;
            return 2 + (W)2 * q;
        }
        const int *g = G[big][e][j & 1];
        v[0] = 4 * q + 2 * j + g[1]; v[1] = 0; v[2] = r - q - g[2]; *t = g[0];
        *st = (W)g[4] + (W)g[5] * q + (W)g[6] * j + (W)4 * q * q + (W)4 * q * j;
        return (W)3 * q + (W)((j + g[3]) / 2);
    }
    return 0;
}

static I M; static uint32_t *ex, *hl; static I *off;
static inline I idx(int t, I a, I r) { I N = a + r; return (t == Y ? off[M + 1] : 0) + off[N] + (a - 3); }
int main(int argc, char **argv) {
  M = atoll(argv[1]);
  off = malloc((M + 2) * sizeof(I)); I tot = 0;
  for (I N = 0; N <= M + 1; N++) { off[N] = tot; if (N >= 5 && N <= M) tot += N - 4; }
  ex = calloc(2 * tot, 4); hl = calloc(2 * tot, 4);
  static I path[1 << 22];
  for (int t0 = y; t0 <= Y; t0 += Y - y) for (I N0 = 5; N0 <= M; N0++) for (I a0 = 3; a0 <= N0 - 2; a0++) {
    if (ex[idx(t0, a0, N0 - a0)] || hl[idx(t0, a0, N0 - a0)]) continue;
    int t = t0; I v[3] = {a0, 0, N0 - a0}; I np = 0; uint32_t e = 0, h = 0; I lastlev = N0;
    for (;;) {
      // at a zigzag start
      I N = v[0] + v[1] + v[2];
      if (N > M) { uint64_t k = ((uint64_t)(t == Y) * 1000003u + (uint64_t)v[0]) * 1000003u + (uint64_t)v[1] * 7919u + (uint64_t)(N - M) * 104729u; k ^= k >> 29; k *= 0x9E3779B97F4A7C15ull; e = (uint32_t)(k >> 33) | 2u; break; }
      lastlev = N;
      if (v[1] == 0) {
        I i = idx(t, v[0], v[2]);
        if (ex[i] || hl[i]) { e = ex[i]; h = hl[i]; break; }
        if (np >= (1 << 22)) { fprintf(stderr, "path too long\n"); return 1; }
        path[np++] = i;
      }
      W st = 0; int halted = 0;
      if (!pass(&t, v, &st)) {
        int hc = -1, n = 0;
        do { if (!jump(&t, v, &st, &hc)) { halted = 1; break; } if (++n > 1000000) { fprintf(stderr, "no zigzag start\n"); return 1; } } while (!zstart(t, v));
      }
      if (halted) { e = 0; h = (uint32_t)lastlev; break; }
    }
    for (I k = 0; k < np; k++) { ex[path[k]] = e; hl[path[k]] = h; }
  }
  FILE *f = fopen(argv[2], "wb"); fwrite(ex, 4, 2 * tot, f); fclose(f);
  f = fopen(argv[3], "wb"); fwrite(hl, 4, 2 * tot, f); fclose(f);
  return 0;
}
