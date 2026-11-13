/* The phase boundaries of 1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB: the run extends the visited tape either only at
   the left end (a round-trip phase) or only at the right end (a right phase).  Each time the side changes, print
   the step and the tape compressed into repeated words (periods up to 16, at least 3 copies; `S>` is the head),
   and the number of extensions and last step of the phase that ended.

   build:  gcc -O2 -o boundaries holdouts/1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB/c/boundaries.c
   usage:  ./boundaries STEPS        (3e10 takes about two minutes; the tape array is 1 GB) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1L << 30)
static unsigned char *tape;
static char buf[1 << 16];

static void rle(long lo, long hi, long h, int st) {
  long i = lo; int n = 0;
  while (i <= hi) {
    if (i == h) n += sprintf(buf + n, "%c> ", "ABCDEF"[st]);
    int bestp = 0; long bestr = 0;
    for (int p = 1; p <= 16; p++) {
      long r = 1;
      while (i + (r + 1) * p - 1 <= hi && !(h > i && h < i + (r + 1) * p) && !memcmp(tape + i, tape + i + r * p, p)) r++;
      if (r >= 3 && r * p > bestr * bestp + p) { bestp = p; bestr = r; }
    }
    if (bestp) {
      n += sprintf(buf + n, "(");
      for (int k = 0; k < bestp; k++) buf[n++] = '0' + tape[i + k];
      n += sprintf(buf + n, ")^%ld ", bestr); i += bestr * bestp;
    } else { buf[n++] = '0' + tape[i]; buf[n++] = ' '; i++; }
    if (n > 60000) { n += sprintf(buf + n, "..."); break; }
  }
  buf[n] = 0;
}

int main(int argc, char **argv) {
  const char *M = "1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB";
  if (argc < 2) { fprintf(stderr, "usage: boundaries STEPS\n"); return 1; }
  long long T = (long long)atof(argv[1]);
  tape = calloc(N, 1);
  int W[12], D[12], S[12];
  for (int s = 0; s < 6; s++) for (int y = 0; y < 2; y++) {
    const char *p = M + s * 7 + y * 3; int i = s * 2 + y;
    if (p[0] == '-') { S[i] = -1; continue; }
    W[i] = p[0] - '0'; D[i] = p[1] == 'R' ? 1 : -1; S[i] = p[2] - 'A';
  }
  long h = N / 2, lo = h, hi = h; int st = 0, side = -1; long long t = 0, cnt = 0, lastt = 0;
  while (t < T) {
    int i = st * 2 + tape[h];
    if (S[i] < 0) { printf("HALT %lld\n", t + 1); return 0; }
    tape[h] = W[i]; h += D[i]; st = S[i]; t++;
    int ev = -1;
    if (h > hi) { hi = h; ev = 1; }
    if (h < lo) { lo = h; ev = 0; }
    if (ev >= 0) {
      if (ev != side) {
        if (side >= 0) printf("  last %c #%lld %lld\n", "LR"[side], cnt, lastt);
        rle(lo, hi, h, st);
        printf("%lld first %c: %s\n", t, "LR"[ev], buf); fflush(stdout);
        side = ev; cnt = 0;
      }
      cnt++; lastt = t;
    }
    if (h < 2 || h > N - 3) { printf("tape full at %lld\n", t); return 1; }
  }
  return 0;
}
