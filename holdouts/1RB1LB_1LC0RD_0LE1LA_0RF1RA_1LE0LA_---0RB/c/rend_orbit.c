/* The right end of 1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB, followed exactly to depth L (see py/rend_cycle.py).

   Locality: a round trip writes each cell from that cell and the one three to its right, so a suffix of the tape
   from a cut P changes only (a) when the sweep enters it, by a map of the suffix alone, (b) by a turn at P - 1,
   which needs c[P] = 0, or (c) when a right sweep arrives at P in token mode (a lone 1 further left). If the suffix
   starts 1 1, then (b) cannot happen and the cell before the cut cannot matter in (a): no lone 1 at P, no 00 at P - 1.

   This program keeps the last cells of the tape as a window that always starts with 1 1: after each entry it keeps
   at most L cells (counted back from the rightmost visited cell) and then drops cells from the left until the window
   starts with 1 1. Dropping cells is sound (every suffix obeys the same rule). So, as long as (c) does not happen,
   each entry has exactly one outcome, computed by running the machine on 0 + window + blanks from A on the 0.
   The window has finitely many values, so the sequence of windows is eventually periodic; the program runs it until
   a window repeats and reports the transient, the period, how far the right end grew over one period, and whether
   any window held a lone 1 (other than in its last 20 cells, where the right end keeps one) or a trip halted.

   usage: ./rend_orbit L FILE      FILE: one line of cells, the last cells of a real tape (at least L of them),
                                   e.g. the cells field of a `TL=n ./trips ...` line. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int W[6][2], D[6][2], S[6][2];
static unsigned char *t; static long cap, LMAX, G;
static long entry(unsigned char *w, long n) {
  if (n + 64 > cap) { cap = 2 * (n + 64); t = realloc(t, cap); }
  t[0] = 0; memcpy(t + 1, w, n); memset(t + 1 + n, 0, cap - 1 - n);
  long p = 0, mx = 0; int s = 0;
  for (;;) {
    if (p + 2 >= cap) { long oc = cap; cap *= 2; t = realloc(t, cap); memset(t + oc, 0, cap - oc); }
    int r = t[p]; if (S[s][r] < 0) return -1;
    t[p] = W[s][r]; int d = D[s][r]; s = S[s][r]; p += d; if (p > mx) mx = p;
    if (p < 0) break;
  }
  long hi = mx - 1; if (hi < n - 1) hi = n - 1;
  G += hi - (n - 1);
  long len = hi + 1, st = len > LMAX ? len - LMAX : 0;
  while (st + 1 < len && !(t[1 + st] == 1 && t[2 + st] == 1)) st++;
  memcpy(w, t + 1 + st, len - st); return len - st;
}
static uint64_t hsh(unsigned char *w, long n, uint64_t h) {
  h ^= (uint64_t)n * 0x9e3779b97f4a7c15ULL;
  for (long i = 0; i < n; i++) { h ^= w[i] + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2); }
  return h;
}
int main(int argc, char **argv) {
  const char *T = "1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB";
  for (int i = 0; i < 6; i++) for (int r = 0; r < 2; r++) {
    const char *g = T + 7 * i + 3 * r; if (g[0] == '-') { S[i][r] = -1; continue; }
    W[i][r] = g[0] - '0'; D[i][r] = g[1] == 'R' ? 1 : -1; S[i][r] = g[2] - 'A'; }
  if (argc < 3) { fprintf(stderr, "usage: %s L FILE\n", argv[0]); return 1; }
  LMAX = atol(argv[1]);
  FILE *f = fopen(argv[2], "r"); if (!f) { perror(argv[2]); return 1; }
  char *line = malloc(1 << 22); if (!fgets(line, 1 << 22, f)) return 1; fclose(f);
  long L0 = 0; while (line[L0] == '0' || line[L0] == '1') L0++;
  if (L0 < LMAX) { fprintf(stderr, "need at least L cells\n"); return 1; }
  cap = 1 << 16; t = calloc(cap, 1);
  unsigned char *w = calloc(4 * LMAX + 100, 1); long n = LMAX;
  for (long i = 0; i < n; i++) w[i] = line[L0 - n + i] - '0';
  long st = 0; while (!(w[st] == 1 && w[st + 1] == 1)) st++; memmove(w, w + st, n - st); n -= st;
  long HS = 1L << 25; uint64_t *tab = calloc(2 * HS, 8); long *gat = calloc(HS, 8);
  long nlone = 0;
  for (long it = 0;; it++) {
    for (long i = 1; i + 1 < n - 20; i++) if (w[i] && !w[i - 1] && !w[i + 1]) { nlone++; break; }
    uint64_t h1 = hsh(w, n, 1), h2 = hsh(w, n, 2) | 1; long k = h1 & (HS - 1);
    while (tab[2 * k]) {
      if (tab[2 * k] == h2) {
        long it0 = (long)tab[2 * k + 1], per = it - it0, gp = G - gat[k];
        /* confirm without hashes: replay to the first occurrence, then one period, and compare cell by cell */
        unsigned char *a = calloc(4 * LMAX + 100, 1); long na = LMAX;
        for (long i = 0; i < na; i++) a[i] = line[L0 - na + i] - '0';
        long s0 = 0; while (!(a[s0] == 1 && a[s0 + 1] == 1)) s0++; memmove(a, a + s0, na - s0); na -= s0;
        for (long j = 0; j < it0; j++) na = entry(a, na);
        unsigned char *b = malloc(na); memcpy(b, a, na); long nb = na;
        for (long j = 0; j < per; j++) na = entry(a, na);
        if (na != nb || memcmp(a, b, na)) { printf("hash collision, no conclusion\n"); return 3; }
        printf("L = %ld: transient %ld entries, period %ld entries, right end grows %ld cells per period, "
               "window length %ld; entries with a lone 1 in the window: %ld; no halt\n",
               LMAX, it0, per, gp, n, nlone);
        return 0;
      }
      k = (k + 1) & (HS - 1);
    }
    tab[2 * k] = h2; tab[2 * k + 1] = it; gat[k] = G;
    if (it > HS / 2) { printf("L = %ld: no repeat within %ld entries\n", LMAX, it); return 2; }
    n = entry(w, n);
    if (n < 0) { printf("L = %ld: HALT at entry %ld\n", LMAX, it); return 1; }
  }
}
