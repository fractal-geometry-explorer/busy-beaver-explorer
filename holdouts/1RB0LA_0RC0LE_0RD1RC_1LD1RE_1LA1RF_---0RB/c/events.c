/* The moments when 1RB0LA_0RC0LE_0RD1RC_1LD1RE_1LA1RF_---0RB starts a new last block.

   At its right-end turns the tape is a list of runs of b = 110 with short separators (c = 10, single cells); the
   last run grows by two copies every round trip.  Now and then a carry reaches the end and a new last run starts
   (the tape ends `... 10 110 10` with the head in state D).  For each such moment print the step and the tape,
   `bN` for b repeated N times (N >= 2), `b` for one copy, `c` for 10, other cells as 0/1.

   build:  gcc -O2 -o events holdouts/1RB0LA_0RC0LE_0RD1RC_1LD1RE_1LA1RF_---0RB/c/events.c
   usage:  ./events STEPS          (3e10 takes about three minutes; the tape array is 1 GB) */
#include <stdio.h>
#include <stdlib.h>
#define N (1L << 30)
static unsigned char *tape;

static void tok(long lo, long hi) {
  long i = lo; int nb = 0;
  while (i <= hi) {
    if (i + 2 <= hi && tape[i] == 1 && tape[i + 1] == 1 && tape[i + 2] == 0) { nb++; i += 3; continue; }
    if (nb) { if (nb == 1) putchar('b'); else printf("b%d ", nb); nb = 0; }
    if (i + 1 <= hi && tape[i] == 1 && tape[i + 1] == 0) { putchar('c'); i += 2; continue; }
    putchar('0' + tape[i]); i++;
  }
  if (nb) { if (nb == 1) putchar('b'); else printf("b%d ", nb); }
  putchar('\n'); fflush(stdout);
}

int main(int argc, char **argv) {
  const char *M = "1RB0LA_0RC0LE_0RD1RC_1LD1RE_1LA1RF_---0RB";
  if (argc < 2) { fprintf(stderr, "usage: events STEPS\n"); return 1; }
  long long T = (long long)atof(argv[1]);
  tape = calloc(N, 1);
  int W[12], D[12], S[12];
  for (int s = 0; s < 6; s++) for (int y = 0; y < 2; y++) {
    const char *p = M + s * 7 + y * 3; int i = s * 2 + y;
    if (p[0] == '-') { S[i] = -1; continue; }
    W[i] = p[0] - '0'; D[i] = p[1] == 'R' ? 1 : -1; S[i] = p[2] - 'A';
  }
  long h = N / 2, lo = h, hi = h; int st = 0; long long t = 0;
  while (t < T) {
    int i = st * 2 + tape[h];
    if (S[i] < 0) { printf("HALT %lld\n", t + 1); return 0; }
    tape[h] = W[i]; h += D[i]; st = S[i]; t++;
    if (h < lo) lo = h;
    if (h > hi) {
      hi = h;
      if (st == 3 && h > lo + 9 && tape[h - 1] == 0 && tape[h - 2] == 1 && tape[h - 3] == 0 && tape[h - 4] == 1 &&
          tape[h - 5] == 1 && tape[h - 6] == 0 && tape[h - 7] == 1 && !(tape[h - 8] == 1 && tape[h - 9] == 1)) {
        printf("%lld ", t); tok(lo, hi - 1);
      }
    }
    if (h < 2 || h > N - 3) { printf("tape full at %lld\n", t); return 1; }
  }
  return 0;
}
