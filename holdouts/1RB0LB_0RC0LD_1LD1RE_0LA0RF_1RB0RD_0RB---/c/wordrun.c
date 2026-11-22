// wordrun.c: the visit law of the 1RB0LB_0RC0LD family run on words, one pass per round, with counts.
//
// A round puts 1 0 in front of the word and makes one visit; a visit to a block with n visits is done at once:
//   0 x     n -> 1 x, n-1                   (one visit, nothing nested)
//   100 x, 110 x   n -> b 0 0 x', 1 + (n-1)/2 visits go on to x   (b = parity of n-1)
//   1010 x  n -> 1010 x', 2n visits go on to x
//   1011 x  n -> 0001 x, n-1                (PR59 machines: halt)
//   111 x   halt (1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA---); 1111 halt, 11101 -> 10101 (one visit),
//           11100 not decoded (1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---)
// These are the rules of lean/Visit.lean, and lean/Word.lean proves that the same pass with exact counts is what the
// machine does.  Counts are exact (128 bit) or 2^e - c with e > 100 and c < 2^100 (only c matters for the cells).
//
// usage: gcc -O2 -o wordrun wordrun.c && ./wordrun MODE ROUNDS [EVERY [DUMP]]
//   MODE pr59 | 0LF (1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA---) | 0RD (1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---)
// stdout: one line per event: JUNK (a count dies on a 0 just left of a 1, which makes the only 11 a word can have),
//   then the word end for the next rounds (END), 1011, 111, HALT; stderr: progress every EVERY rounds.
//   DUMP: write the word after the last round to this file (one line of cells).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef unsigned __int128 u128;
static uint8_t *T; static long F, E;  // the word is T[F..E), zeros after E
static const long N = 1L << 28;
static void show(long a, long b) { putchar('|'); for (long i = a; i < b; i++) putchar('0' + T[i]); putchar('|'); }
int main(int argc, char **argv) {
  setvbuf(stdout, NULL, _IOLBF, 0);
  if (argc < 3) { fprintf(stderr, "usage: %s pr59|0LF|0RD ROUNDS [EVERY]\n", argv[0]); return 2; }
  int mode = !strcmp(argv[1], "pr59") ? 0 : !strcmp(argv[1], "0LF") ? 1 : !strcmp(argv[1], "0RD") ? 2 : -1;
  if (mode < 0) { fprintf(stderr, "bad mode\n"); return 2; }
  long R = atol(argv[2]), every = argc > 3 ? atol(argv[3]) : 10000;
  T = calloc(N, 1); F = N / 4; E = F + 1; T[F] = 1;
  long njunk = 0, n1011 = 0, watch = 0;
  for (long r = 1; r <= R; r++) {
    F -= 2; T[F] = 1; T[F + 1] = 0;
    long p = F, e = 0; int big = 0; u128 c = 1;  // the count: big ? 2^e - c : c
    long oldE = E;
    while (big || c > 0) {
      if (p + 8 >= N) { fprintf(stderr, "tape overflow\n"); return 1; }
      uint8_t *w = T + p;
      if (w[0] == 0) {
        w[0] = 1;
        if (big) c++; else c--;
        if (!big && c == 0 && w[1] == 1) {
          njunk++; watch = 4;
          printf("JUNK round %ld at %ld from end %ld ", r, p - F, oldE - p); show(p - 24 > F ? p - 24 : F, p + 24); printf("\n");
        }
      } else if (w[2] == 0) {  // 100, 110: first visit, then a digit block
        if (big) { u128 c1 = c + 1; w[0] = c1 & 1; e -= 1; c = (c1 + 1) / 2 - 1; }
        else { u128 n1 = c - 1; w[0] = n1 & 1; c = 1 + n1 / 2; }
        w[1] = 0; p += 3;
      } else if (w[1] == 0 && w[3] == 0) {  // 1010
        if (big) e++;
        c *= 2; p += 4;
      } else if (w[1] == 0) {  // 1011
        n1011++;
        printf("1011 round %ld at %ld from end %ld count %s%lu ", r, p - F, oldE - p, big ? "2^e-" : "", (unsigned long)c);
        show(p - 24 > F ? p - 24 : F, p + 24); printf("\n");
        if (mode == 0) { printf("HALT round %ld (1011, as busycoq PR59 proves)\n", r); return 0; }
        w[0] = 0; w[2] = 0; w[3] = 1; if (big) c++; else c--;
        if (!big && c == 0 && w[4] == 1) {
          njunk++; watch = 4;
          printf("JUNK round %ld at %ld from end %ld (after 1011) ", r, p - F, oldE - p); show(p - 24 > F ? p - 24 : F, p + 24); printf("\n");
        }
      } else {  // 111
        printf("111 round %ld at %ld from end %ld count %s%lu ", r, p - F, oldE - p, big ? "2^e-" : "", (unsigned long)c);
        show(p - 24 > F ? p - 24 : F, p + 24); printf("\n");
        if (mode == 1 || w[3] == 1) { printf("HALT round %ld\n", r); return 0; }
        if (w[4] == 1) { w[1] = 0; if (big) c++; else c--; }
        else { printf("STOP round %ld: 11100 is not decoded\n", r); return 0; }
      }
      if (big) { if (e <= 100) { c = (((u128)1) << e) - c; big = 0; } else if (c >> 100) { fprintf(stderr, "c overflow\n"); return 1; } }
      else if (c >> 110) { int k = 0; while (((u128)1 << k) < c) k++; c = (((u128)1) << k) - c; e = k; big = 1; }
    }
    if (p + 4 > E) E = p + 4;
    while (E > F && T[E - 1] == 0) E--;
    if (watch > 0) { watch--; printf("END round %ld died %ld from old end ", r, oldE - p); show(E - 48 > F ? E - 48 : F, E); printf("\n"); }
    if (r % every == 0) fprintf(stderr, "round %ld length %ld junk %ld 1011 %ld\n", r, E - F, njunk, n1011);
  }
  if (argc > 4) { FILE *f = fopen(argv[4], "w"); for (long i = F; i < E; i++) fputc('0' + T[i], f); fputc('\n', f); fclose(f); }
  printf("DONE %ld rounds, junk %ld, 1011 %ld\n", R, njunk, n1011);
  return 0;
}
