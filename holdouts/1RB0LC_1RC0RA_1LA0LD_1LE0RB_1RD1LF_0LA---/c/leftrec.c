// leftrec MACHINE MODE N : the "left-A records" of a machine (the head reaches a new leftmost cell in state A).
//   MODE run N   : run N steps from blank tape; count the left-A records and those at which the tape has a factor 1111.
//   MODE all N   : for every tape w of N cells (blank elsewhere) without a factor 1111, start A on the first cell of w
//                  and run to the next left-A record; count halts, returns, and returns to a tape with a factor 1111.
// gcc -O2 -o leftrec leftrec.c
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int W[6][2], Mv[6][2], Nx[6][2];
static int has1111(unsigned char *t, long a, long b) {
  for (long p = a; p + 3 < b; p++) if (t[p] & t[p + 1] & t[p + 2] & t[p + 3]) return 1;
  return 0;
}
int main(int c, char **v) {
  if (c < 4) { fprintf(stderr, "usage: leftrec MACHINE run|all N\n"); return 1; }
  char *m = v[1];
  for (int i = 0; i < 6; i++) for (int b = 0; b < 2; b++) {
    char *p = m + i * 7 + b * 3;
    if (p[2] == '-') Nx[i][b] = -1; else { W[i][b] = p[0] - '0'; Mv[i][b] = p[1] == 'R' ? 1 : -1; Nx[i][b] = p[2] - 'A'; }
  }
  if (!strcmp(v[2], "run")) {
    long long max = atoll(v[3]); long SZ = 1L << 26; unsigned char *t = calloc(SZ, 1);
    long h = SZ / 2, lo = h; int s = 0; long long c4 = 0, rec = 0, bad = 0;
    for (long long k = 0; k < max; k++) {
      int b = t[h]; if (Nx[s][b] < 0) { printf("HALT %lld\n", k + 1); break; }
      int w = W[s][b];
      if (w != b) {
        for (int o = 0; o < 4; o++) c4 -= t[h - o] & t[h - o + 1] & t[h - o + 2] & t[h - o + 3];
        t[h] = w;
        for (int o = 0; o < 4; o++) c4 += t[h - o] & t[h - o + 1] & t[h - o + 2] & t[h - o + 3];
      }
      h += Mv[s][b]; s = Nx[s][b];
      if (h < lo) { lo = h; if (s == 0) { rec++; if (c4) { bad++; if (bad < 5) printf("1111 at step %lld\n", k + 1); } } }
    }
    printf("left-A records %lld, with a factor 1111: %lld\n", rec, bad);
  } else {
    int L = atoi(v[3]); long cnt[5] = {0}; long maxk = 0; static unsigned char t[1 << 12]; int base = 1 << 11;
    for (long mm = 0; mm < (1L << L); mm++) {
      int ok = 1; for (int i = 0; i + 3 < L; i++) if (((mm >> i) & 15) == 15) { ok = 0; break; }
      if (!ok) continue;
      memset(t, 0, sizeof t); for (int i = 0; i < L; i++) t[base + i] = (mm >> i) & 1;
      long h = base, lo = base; int s = 0; long k = 0; int res = 3;
      while (k < 1000000) {
        int b = t[h]; if (Nx[s][b] < 0) { res = 0; break; }
        t[h] = W[s][b]; h += Mv[s][b]; s = Nx[s][b]; k++;
        if (h < lo) { lo = h; if (s == 0) { res = 1; break; } }
        if (h > base + L + 60) { res = 2; break; }
      }
      if (res == 1) { if (has1111(t, h, base + L + 64)) res = 4; if (k > maxk) maxk = k; }
      cnt[res]++;
    }
    printf("tapes of %d cells without 1111: halt %ld, return %ld (longest %ld steps), of which to a tape with 1111 %ld, "
           "head ran off right %ld, timeout %ld\n", L, cnt[0], cnt[1] + cnt[4], maxk, cnt[4], cnt[2], cnt[3]);
  }
}
