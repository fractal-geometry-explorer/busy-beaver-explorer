/* cascade: the zone orbit as a cascade of one-bit cells (lean/Cascade.lean), for the four machines with the
 * `111110` block (1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA, 1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA,
 * 1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA, 1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB).
 *
 *   cascade STATE M [CAP]
 *
 * STATE is "t n 0 Z" as written by lean/DumpState.lean (Z read from the block outwards; cell j is Z[j]).
 * Events: F (flip), P0, P1.  A cell with bit x:  F -> x := !x;  P0 -> F if x = 0, else P1;  P1 -> P x, x := !x.
 *
 * 1. The stranded block: the longest stretch [a, b) of Z with period 3.  The background stream is the one of the
 *    three period-3 streams of P events that the cells [a, b) pass on unchanged (no F, bits back after 3 events).
 * 2. The old zone alone: the cells [b, |Z|) fed the background stream until an event leaves the last cell
 *    (P: a reset, F: a halt; lean/Cascade.lean, swr_feed_reset / swr_feed_halt) or the cells are back.
 * 3. The front: W_m, the events entering cell m during one period of the cells [0, m) (W_0 = the block's three
 *    letters; W_{m+1} = cell m applied to W_m, twice when its bit is not back: lean/Cascade.lean, cell_bit),
 *    for m = a .. M, with the first index at which W_m differs from the background stream at cut m.  The old
 *    zone sees exactly the background for as many passes as the front index at cut b.
 * Build: gcc -O2 -o cascade cascade.c */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned char Z[1 << 20];

/* one cell: e in {0 = F, 1 = P0, 2 = P1}; returns the event that goes on (3 = none) */
static inline unsigned char cell(unsigned char *x, unsigned char e) {
  if (e == 0) { *x ^= 1; return 3; }
  if (e == 1) return *x ? 2 : 0;
  unsigned char o = *x ? 2 : 1; *x ^= 1; return o;
}

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: cascade STATE M [CAP]\n"); return 2; }
  FILE *f = fopen(argv[1], "r"); unsigned long long t, n; long rl;
  if (!f || fscanf(f, "%llu %llu %ld ", &t, &n, &rl) != 3 || rl != 0) { fprintf(stderr, "bad state\n"); return 2; }
  long L = 0; int ch; while ((ch = fgetc(f)) == '0' || ch == '1') Z[L++] = ch - '0';
  int M = atoi(argv[2]); long CAP = argc > 3 ? atol(argv[3]) : 400000000L;

  long a = 0, b = 0;
  for (long i = 0; i < L;) { long j = i; while (j + 3 < L && Z[j + 3] == Z[j]) j++;
    if (j + 3 - i > b - a) { a = i; b = j + 3; } i = j + 1; }
  printf("word %ld cells: zone [0,%ld), stranded block [%ld,%ld) (%ld cells), old zone [%ld,%ld) (%ld cells)\n",
         L, a, a, b, b - a, b, L, L - b);

  unsigned char bg0[3], bg[3]; int ph;
  for (ph = 0; ph < 3; ph++) {
    for (int i = 0; i < 3; i++) bg[i] = ((ph + i) % 3 != 2) ? 2 : 1;
    memcpy(bg0, bg, 3); int ok = 1;
    for (long m = a; m < b && ok; m++) { unsigned char x = Z[m], o[3]; int no = 0;
      for (int i = 0; i < 3; i++) { unsigned char e = cell(&x, bg[i]); if (e == 3 || e == 0) { ok = 0; break; } o[no++] = e; }
      if (x != Z[m]) ok = 0;
      memcpy(bg, o, 3); }
    if (ok) break;
  }
  if (ph == 3) { printf("no background stream\n"); return 1; }
  printf("background stream entering the old zone: %c%c%c\n", "F01"[bg[0]], "F01"[bg[1]], "F01"[bg[2]]);

  { unsigned char *s = malloc(L - b); memcpy(s, Z + b, L - b); long tick = 0; int out = 3;
    for (;;) { for (int i = 0; i < 3 && out == 3; i++) { unsigned char e = bg[i];
        for (long j = 0; j < L - b && e != 3; j++) e = cell(&s[j], e);
        tick++; if (e != 3) out = e; }
      if (out != 3) { printf("old zone alone: an event leaves at tick %ld: %s\n", tick, out == 0 ? "HALT" : "RESET"); break; }
      if (memcmp(s, Z + b, L - b) == 0) { printf("old zone alone: back after %ld ticks, nothing leaves\n", tick); break; } }
    free(s); }

  unsigned char *W = malloc(CAP), *W2 = malloc(CAP); long N = 3;
  for (int i = 0; i < 3; i++) W[i] = ((n + i) % 3 != 2) ? 2 : 1;
  memcpy(bg, bg0, 3);
  for (long m = 0; m < M && m < L; m++) {
    if (m >= a) { long d = -1, nf = 0;
      for (long i = 0; i < N; i++) { if (d < 0 && W[i] != bg[i % 3]) d = i; nf += W[i] == 0; }
      printf("cut %ld: |W| = %ld (F %ld), front index %ld\n", m, N, nf, d); fflush(stdout);
      unsigned char x = Z[m], o[3]; for (int i = 0; i < 3; i++) o[i] = cell(&x, bg[i]); memcpy(bg, o, 3); }
    unsigned char x0 = Z[m], x = x0; long K = 0;
    do { for (long i = 0; i < N; i++) { unsigned char e = cell(&x, W[i]);
        if (e != 3) { if (K >= CAP) { printf("CAP reached at cut %ld\n", m); return 0; } W2[K++] = e; } }
    } while (x != x0);
    unsigned char *tmp = W; W = W2; W2 = tmp; N = K;
  }
  return 0;
}
