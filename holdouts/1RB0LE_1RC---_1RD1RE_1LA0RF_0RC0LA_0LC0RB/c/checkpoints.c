/* Check the macro replay of 1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB against the plain simulation: for each line
   "STEP STATE OFFSET BITS" of the file (from `py/macro.py --checkpoints`), run to STEP and compare the state and the
   whole tape (BITS, with the head on bit OFFSET, and blank everywhere else).

   build:  gcc -O2 -o checkpoints holdouts/1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB/c/checkpoints.c
   usage:  ./checkpoints FILE      (one core; the tape array is 1 GB; 3e10 steps take a few minutes) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1L << 30)
static unsigned char *tape;
static char line[1 << 22];

int main(int argc, char **argv) {
  const char *M = "1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB";
  if (argc < 2) { fprintf(stderr, "usage: checkpoints FILE\n"); return 2; }
  FILE *f = fopen(argv[1], "r");
  if (!f) { perror(argv[1]); return 2; }
  tape = calloc(N, 1);
  int W[12], D[12], S[12];
  for (int s = 0; s < 6; s++) for (int y = 0; y < 2; y++) {
    const char *p = M + s * 7 + y * 3; int i = s * 2 + y;
    if (p[0] == '-') { S[i] = -1; continue; }
    W[i] = p[0] - '0'; D[i] = p[1] == 'R' ? 1 : -1; S[i] = p[2] - 'A';
  }
  long h = N / 2, lo = h, hi = h; int st = 0, ok = 0, bad = 0, cs; long long t = 0, ct; long off;
  while (fscanf(f, "%lld %d %ld %s", &ct, &cs, &off, line) == 4) {
    while (t < ct) {
      int i = st * 2 + tape[h];
      if (S[i] < 0) { printf("HALT at %lld\n", t + 1); return 1; }
      tape[h] = W[i]; h += D[i]; st = S[i]; t++;
      if (h < lo) lo = h;
      if (h > hi) hi = h;
      if (h < 2 || h > N - 3) { printf("tape full at %lld\n", t); return 1; }
    }
    long len = strlen(line), base = h - off; int good = st == cs;
    for (long k = 0; k < len && good; k++) if (tape[base + k] != line[k] - '0') good = 0;
    for (long k = lo; k <= hi && good; k++) if (tape[k] && (k < base || k >= base + len)) good = 0;
    printf("%lld %s\n", ct, good ? "ok" : "MISMATCH");
    fflush(stdout);
    if (good) ok++; else bad++;
  }
  printf("%d checkpoints agree, %d differ\n", ok, bad);
  return bad > 0;
}
