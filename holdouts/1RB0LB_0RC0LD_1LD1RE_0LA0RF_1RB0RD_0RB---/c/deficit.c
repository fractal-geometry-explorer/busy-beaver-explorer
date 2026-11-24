// deficit.c: the word pass of the 1RB0LB_0RC0LD family in deficit form (lean/Deficit.lean, visd).
//
// The count of visits is written n = 2^e - c.  The level e starts at 0 (count 1) in every round, goes up by one at
// every doubler 1010 and down by one at every digit block 1?0 (not below 0); the deficit c is small:
//   a 0 at a block start      -> 1, c + 1                    (the pass then reads that cell again)
//   a digit block 1?0         -> b00 with b = 1 iff c is even (b = 0 at level 0), c / 2 (rounded down)
//   a doubler 1010            -> unchanged, 2c
//   1011 -> 0001, c + 1 (then the 0 takes a visit as above);  1111 halt;  11101 -> 10101, c + 1;  11100 has no proved rule (stop)
// and the pass ends when c = 2^e.  lean/Deficit.lean proves (visd_eq) that this is the pass of lean/Word.lean and
// c/wordrun.c with the exact count 2^e - c.  The deficit needs no big numbers: it is at most a few thousand here.
//
// usage: gcc -O2 -o deficit deficit.c && ./deficit ROUNDS [EVERY [DUMP]]
// stdout: the histogram of c over all block starts of all rounds, the largest c (with round and place), and for every
//   junk event (the pass ends on a 0 with a 1 right after it, the only way two 1s can touch) the last blocks of
//   that round as distance-from-end:block:level:deficit.  DUMP: the word after the last round (compare with
//   ./wordrun 0RD ROUNDS 1 DUMP; the two files must be equal).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static uint8_t *T; static long F, E; static const long N = 1L << 28;
#define HMAX 8192
static long hist[HMAX], big; static long cmax, cmax_r, cmax_d;
#define KEEP 16
#define REPORT(q) do { njunk++; \
    printf("JUNK round %ld, %ld cells from the end:", r, oldE - (q)); \
    for (int i = nk > 8 ? nk - 8 : 0; i < nk; i++) printf(" %ld%c:%ld:%ld", oldE - kp[i % KEEP], kk[i % KEEP], ke[i % KEEP], kc[i % KEEP]); \
    printf(" | end at %ld, level %ld\n", oldE - (q), e); } while (0)
int main(int argc, char **argv) {
  setvbuf(stdout, NULL, _IOLBF, 0);
  if (argc < 2) { fprintf(stderr, "usage: %s ROUNDS [EVERY [DUMP]]\n", argv[0]); return 2; }
  long R = atol(argv[1]), every = argc > 2 ? atol(argv[2]) : 10000;
  T = calloc(N, 1); F = N / 4; E = F + 1; T[F] = 1;
  long njunk = 0;
  for (long r = 1; r <= R; r++) {
    F -= 2; T[F] = 1; T[F + 1] = 0;
    long p = F, e = 0, c = 0, oldE = E;
    long kp[KEEP], ke[KEEP], kc[KEEP]; char kk[KEEP]; int nk = 0;
    for (;;) {
      if (e < 62 && c == (1L << e)) break;      // no visit left
      if (p + 8 >= N) { fprintf(stderr, "tape overflow\n"); return 1; }
      uint8_t *w = T + p;
      if (w[0] == 0) {
        w[0] = 1; c++;
        if (e < 62 && c == (1L << e) && w[1] == 1) REPORT(p);
        continue;
      }
      char k = w[2] == 0 ? 'd' : (w[1] == 0 && w[3] == 0) ? 'L' : w[1] == 0 ? 'x' : '!';
      if (c < HMAX) hist[c]++; else big++;
      if (c > cmax) { cmax = c; cmax_r = r; cmax_d = oldE - p; }
      kp[nk % KEEP] = p; ke[nk % KEEP] = e; kc[nk % KEEP] = c; kk[nk % KEEP] = k; nk++;
      if (k == 'd') {
        w[0] = e == 0 ? 0 : !(c & 1); w[1] = 0;
        if (e > 0) { e--; c /= 2; }
        p += 3;
      } else if (k == 'L') { e++; c *= 2; p += 4; }
      else if (k == 'x') {                                             // 1011 -> 0001 takes one visit
        w[0] = 0; w[2] = 0; w[3] = 1; c++;
        printf("1011 round %ld, %ld cells from the end, level %ld deficit %ld\n", r, oldE - p, e, c - 1);
        if (e < 62 && c == (1L << e) && w[4] == 1) REPORT(p + 3);  // the pass ends on 0001 before a 1
      }
      else {
        if (w[3] == 1) { printf("HALT round %ld (1111)\n", r); return 0; }
        if (w[4] == 1) { w[1] = 0; c++; }                              // 11101 -> 10101
        else { printf("STOP round %ld: 11100 has no proved rule\n", r); return 0; }
      }
      if (c > (1L << 40)) { fprintf(stderr, "deficit too large\n"); return 1; }
    }
    if (p + 4 > E) E = p + 4;
    while (E > F && T[E - 1] == 0) E--;
    if (r % every == 0) fprintf(stderr, "round %ld length %ld junk %ld max deficit %ld\n", r, E - F, njunk, cmax);
  }
  long tot = big; for (int i = 0; i < HMAX; i++) tot += hist[i];
  printf("DONE %ld rounds, %ld block starts, junk %ld, largest deficit %ld (round %ld, %ld cells from the end)\n", R, tot, njunk, cmax, cmax_r, cmax_d);
  long acc = 0;
  for (int i = 0; i < HMAX; i++) if (hist[i]) { acc += hist[i]; printf("c=%d %ld (%.6f cumulative)\n", i, hist[i], (double)acc / tot); }
  if (argc > 3) { FILE *f = fopen(argv[3], "w"); for (long i = F; i < E; i++) fputc('0' + T[i], f); fputc('\n', f); fclose(f); }
  return 0;
}
