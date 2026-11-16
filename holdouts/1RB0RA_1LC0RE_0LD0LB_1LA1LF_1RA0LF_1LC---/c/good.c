/* The condition of lean/Lockstep.lean on a plain cell simulator: the head never reads a 1 in state A or B with only
   0s to its left.  The table of 1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---, started in state START (0..5 for A..F:
   3 is the run of 1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE--- mirrored, `Good40600`; 0 is this machine, `Good`).

   usage: gcc -O2 -o good holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/c/good.c && ./good START STEPS
   (1e11 steps: about 9 minutes) */
#include <stdio.h>
#include <stdlib.h>
static const int W[6][2] = {{1, 0}, {1, 0}, {0, 0}, {1, 1}, {1, 0}, {1, -1}};
static const int Mv[6][2] = {{1, 1}, {-1, 1}, {-1, -1}, {-1, -1}, {1, -1}, {-1, 0}};
static const int Nx[6][2] = {{1, 0}, {2, 4}, {3, 1}, {0, 5}, {0, 5}, {2, -1}};
int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: good START STEPS\n"); return 2; }
  int q = atoi(argv[1]);
  long long N = (long long)atof(argv[2]), s;
  long SZ = 1L << 26, pos = SZ / 2, lo1 = SZ, bad = 0;   /* lo1: the leftmost 1 (SZ: none yet) */
  unsigned char *t = calloc(SZ, 1);
  for (s = 0; s < N; s++) {
    int b = t[pos];
    if (b == 1 && pos == lo1 && q <= 1) { bad++; if (bad < 10) printf("BAD at step %lld, state %c\n", s, 'A' + q); }
    int nq = Nx[q][b];
    if (nq < 0) { printf("HALT at step %lld\n", s); break; }
    int w = W[q][b];
    t[pos] = w;
    if (w == 1 && pos < lo1) lo1 = pos;
    if (w == 0 && pos == lo1) { long p = pos; while (p < SZ && t[p] == 0) p++; lo1 = p; }
    pos += Mv[q][b]; q = nq;
    if (pos < 1 || pos >= SZ - 1) { printf("out of tape at step %lld\n", s); return 1; }
  }
  printf("start %c, %lld steps, configurations excluded by the condition: %ld\n", 'A' + atoi(argv[1]), s, bad);
  return bad != 0;
}
