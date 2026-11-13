// The counter of 1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC, run to the first time its carry reaches the far end.
//
// 1. Runs the machine from blank tape for 2*10^7 steps (plain simulation) and keeps the configuration at the last
//    sweep's arrival: A reading the cell x0 of the counter, 220 cells from the right end, with n0 pairs `10` of wall
//    on its left.
// 2. Checks that the counter cells are x0 1 x1 1 ... x110 (a 1 on every odd cell) and then iterates the 4-state
//    automaton of README.md ("The counter") on x1..x110, once per sweep, printing each new depth of the carry, until
//    the carry runs past x110 (or MAX sweeps).  Before that the plain machine and the automaton agree sweep for
//    sweep (py/automaton.py checks this on the first 2,500 sweeps; README.md).
// 3. Prints the wall length then, the state the carry arrives in, the counter before that sweep, and an estimate of
//    the step count (3 n^2: each sweep crosses the wall twice, 6n + 4 steps).
//
// usage: gcc -O2 -o counter counter.c && ./counter [MAX]       (about a minute)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1 << 22)
static unsigned char tape[N];
static const int O[4][2] = {{1, 0}, {0, 1}, {1, 0}, {0, 1}}, NX[4][2] = {{1, 2}, {1, 1}, {0, 3}, {3, 0}};
int main(int argc, char **argv) {
  const char *m = "1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC";
  long long MAX = argc > 1 ? atoll(argv[1]) : 100000000000LL;
  int nw[6][2], mv[6][2], ns[6][2];
  for (int s = 0; s < 6; s++)
    for (int r = 0; r < 2; r++) {
      const char *t = m + s * 7 + r * 3;
      if (t[0] == '-') { ns[s][r] = -1; continue; }
      nw[s][r] = t[0] - '0'; mv[s][r] = t[1] == 'R' ? 1 : -1; ns[s][r] = t[2] - 'A';
    }
  long pos = N / 2, lo = pos, hi = pos; int st = 0, run = 0;
  long long snap_step = 0; long snap_pos = 0, snap_lo = 0;
  static unsigned char x[200];
  for (long long i = 0; i < 20000000; i++) {
    int r = tape[pos]; int q = ns[st][r];
    if (q < 0) { printf("halted at step %lld\n", i); return 1; }
    tape[pos] = nw[st][r]; int d = mv[st][r]; pos += d; st = q;
    if (pos < lo) lo = pos;
    if (pos > hi) hi = pos;
    run = d == 1 ? run + 1 : 0;
    if (st == 0 && tape[pos] == 1 && run >= 100 && hi - pos == 220) { snap_step = i + 1; snap_pos = pos; snap_lo = lo; }
  }
  // re-run to the snapshot (simplest way to have the tape as it was)
  memset(tape, 0, sizeof tape); pos = N / 2; lo = hi = pos; st = 0;
  for (long long i = 0; i < snap_step; i++) {
    int r = tape[pos]; int q = ns[st][r]; tape[pos] = nw[st][r]; pos += mv[st][r]; st = q;
    if (pos < lo) lo = pos;
    if (pos > hi) hi = pos;
  }
  long n0 = (snap_pos - snap_lo) / 2;
  for (long j = snap_lo; j < snap_pos; j += 2)
    if (tape[j] != 1 || tape[j + 1] != 0) { printf("wall is not (10)^n\n"); return 1; }
  for (int j = 0; j <= 220; j++) if (j % 2 == 1 && tape[snap_pos + j] != 1) { printf("odd cell %d is 0\n", j); return 1; }
  int K = 111;
  for (int j = 0; j < K; j++) x[j] = tape[snap_pos + 2 * j];
  printf("snapshot: step %lld, wall (10)^%ld, counter x0..x110 =\n  ", snap_step, n0);
  for (int j = 0; j < K; j++) putchar('0' + x[j]);
  putchar('\n');
  int rec = 0; unsigned char sv[200];
  const char *SN = "aebc";
  for (long long it = 0; it < MAX; it++) {
    memcpy(sv, x, K);
    int q = 0, j = 1;
    for (; j < K; j++) { int d = x[j]; x[j] = O[q][d]; q = NX[q][d]; if (q == 1) break; }
    if (j > rec) { rec = j; printf("sweep %lld (wall %lld): the carry reaches x%d\n", it, n0 + it, j < K ? j : K - 1); fflush(stdout); }
    if (j >= K) {
      long double n = (long double)(n0 + it);
      printf("the carry runs past x110 in state %c at sweep %lld after the snapshot: wall (10)^%lld\n", SN[q], it, n0 + it);
      printf("counter before that sweep: "); for (int k = 0; k < K; k++) putchar('0' + sv[k]); putchar('\n');
      printf("steps from blank tape: about %.3Le\n", 3.0L * n * n);
      return 0;
    }
  }
  printf("no carry past x110 in %lld sweeps\n", MAX);
  return 0;
}
