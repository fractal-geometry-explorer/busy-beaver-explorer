// fast direct stepping for cjump.py (ctypes).  Returns 0: budget used, 1: event (config before the turning step),
// 2: halt (the halting step counted), 3: head too close to the buffer edge (grow and call again).
#include <stdint.h>
int cj_run(uint8_t *c, int64_t N, int64_t off, int64_t *hp, int *sp, int64_t *done, int *dp, int64_t *lop, int64_t *hip,
           const int *tab, int64_t budget, int64_t P, int S, int R, int *firstp, int64_t *hist, int64_t hbase, int64_t hlen) {
  int64_t h = *hp, lo = *lop, hi = *hip, k = 0; int s = *sp, d = *dp, first = *firstp;
  int ret = 0;
  while (k < budget) {
    int64_t i = h + off;
    if (i <= 1 || i >= N - 2) { ret = 3; break; }
    int r = c[i]; const int *t = tab + 3 * (2 * s + r);
    if (t[2] < 0) { k++; ret = 2; break; }
    int nd = t[1];
    if (nd == 1 && d == -1) {
      if (hist) { int64_t j = h - hbase; if (j >= 0 && j < hlen) hist[j * 16 + 2 * s + r]++; }
      if (h == P && s == S && r == R) { if (first) first = 0; else { ret = 1; break; } }
    }
    c[i] = (uint8_t)t[0]; s = t[2]; k++; h += nd; d = nd;
    if (h < lo) lo = h; else if (h > hi) hi = h;
  }
  *firstp = first; *hp = h; *sp = s; *done = k; *dp = d; *lop = lo; *hip = hi;
  return ret;
}
