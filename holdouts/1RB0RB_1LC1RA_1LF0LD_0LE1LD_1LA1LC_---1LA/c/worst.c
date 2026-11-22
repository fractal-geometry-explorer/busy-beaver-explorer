/* worst: the fewest events that get a disturbance through k cells of the stranded block, over ALL input streams.
 *
 *   worst K        (K a multiple of 3, K <= 63)
 *
 * The four F08 machines with the `111110` block have the cascade of lean/Cascade.lean; the stranded block is a run
 * of cells with bits 1 0 1 repeated (from its first cell, next to the new zone).  Fed the background P1 P1 P0
 * repeated, such a run passes every event on unchanged (lean/FrontWorst.lean, block_passes_background).
 * This program does a breadth-first search over the states (bits of the K cells, number of events let out mod 3),
 * starting from the block's own bits, with any of F, P0, P1 as the next event entering the first cell, until an
 * event leaves the last cell that is not the next event of the background.  It prints the length of the shortest
 * such stream and one stream of that length (F, 0 = P0, 1 = P1).
 * Results (22 Nov 2026): K = 3 6 9 12 15 18 21 24 27 30 33 36 -> 3 6 9 12 18 25 34 41 50 60 73 88 events.
 * K = 36 visits 2.7e8 states and needs about 9 GB.  lean/FrontWorst.lean checks the stream found for K = 36.
 * Build: gcc -O2 -o worst worst.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static inline int cellf(int *x, int e) { if (e == 0) { *x ^= 1; return 3; } if (e == 1) return *x ? 2 : 0; int o = *x ? 2 : 1; *x ^= 1; return o; }
#define TB 30
#define QMAX 600000000L
static unsigned *tab; static uint64_t *q; static long qt = 0;
/* insert state key (queue index qt); 0 if already present */
static int ins(uint64_t key) { uint64_t h = ((key + 1) * 0x9E3779B97F4A7C15ULL) >> (64 - TB);
  while (tab[h]) { if (q[tab[h] - 1] == key) return 0; h = (h + 1) & ((1ULL << TB) - 1); } tab[h] = qt + 1; return 1; }
int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: worst K\n"); return 2; }
  int k = atoi(argv[1]); if (k % 3 || k <= 0 || k > 63) { fprintf(stderr, "K must be a multiple of 3, at most 63\n"); return 2; }
  int bgout[3] = {2, 2, 1};               /* encoding: 0 = F, 1 = P0, 2 = P1, 3 = nothing goes on */
  uint64_t ideal = 0; for (int j = 0; j < k; j++) if (j % 3 != 1) ideal |= 1ULL << j;
  tab = calloc(1ULL << TB, 4); q = malloc(8 * QMAX); unsigned *pq = malloc(4 * QMAX); unsigned char *pe = malloc(QMAX);
  if (!tab || !q || !pq || !pe) { fprintf(stderr, "out of memory\n"); return 1; }
  ins(ideal * 3); q[qt] = ideal * 3; pq[qt] = 0xffffffffu; qt++;
  long qh = 0; int d = 0;
  while (qh < qt) { long end = qt; d++;
    for (; qh < end; qh++) { uint64_t c = q[qh], b = c / 3; int ph = c % 3;
      for (int e0 = 0; e0 < 3; e0++) { uint64_t st = b; int e = e0;
        for (int j = 0; j < k && e != 3; j++) { int x = (st >> j) & 1; e = cellf(&x, e); st = (st & ~(1ULL << j)) | ((uint64_t)x << j); }
        int nph = ph;
        if (e != 3) { if (e != bgout[ph]) {
            printf("K = %d: fewest events %d (states visited %ld); one stream: ", k, d, qt);
            char buf[512]; int L = 0; buf[L++] = "F01"[e0];
            for (long z = qh; pq[z] != 0xffffffffu; z = pq[z]) buf[L++] = "F01"[pe[z]];
            for (int i = L - 1; i >= 0; i--) putchar(buf[i]);
            printf(" (lets out %c where the background has %c)\n", "F01"[e], "F01"[bgout[ph]]); return 0; }
          nph = (ph + 1) % 3; }
        uint64_t n = st * 3 + nph;
        if (ins(n)) { if (qt >= QMAX) { printf("K = %d: more than %d events (queue full)\n", k, d); return 0; }
          q[qt] = n; pq[qt] = qh; pe[qt] = e0; qt++; } } } }
  printf("K = %d: no stream gets through\n", k); return 0;
}
