#include "../../../tools/c/tm.h"
/* lockstep STEPS: the runs of the table of 1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE from state A (this machine) and
   from state C (1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC, mirrored), compared at every visit of the head, in state
   C, to the left end of the tape: the tape of the second run must be the tape of the first followed by the word
   10001101, from step 2 of the first run and step 49 of the second on (the visits of the second run before step 49
   have no partner; see at_A, at_C in lean/Lockstep.lean).  Prints the number of visits compared and of mismatches (exit code 1 if any).  STEPS for each run. */
static int next(tm_machine *m, tm_tape *t, int *st, long long *k, long long max) {
  while (*k < max) {
    if (!tm_step(m, t, st)) return -1;
    (*k)++;
    if (*st == 2 && t->head == t->lo) return 1;
  }
  return 0;
}
static long long last_one(tm_tape *t) { long long p = t->hi; while (p >= t->lo && !tm_get(t, p)) p--; return p; }
int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: lockstep STEPS\n"); return 2; }
  tm_machine m; tm_parse("1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE", &m);
  long long max = (long long)atof(argv[1]), ka = 0, kc = 0, n = 0, bad = 0;
  tm_tape a, c; tm_tape_init(&a, 1 << 22); tm_tape_init(&c, 1 << 22);
  int sa = 0, sc = 2; const char *W = "10001101";
  int ra = next(&m, &a, &sa, &ka, max), rc = next(&m, &c, &sc, &kc, max);
  while (rc == 1 && kc < 49) rc = next(&m, &c, &sc, &kc, max);
  while (ra == 1 && rc == 1) {
    long long la = last_one(&a) - a.lo, lc = last_one(&c) - c.lo;
    int eq = la + 8 == lc;
    for (long long i = 0; eq && i <= la; i++) if (tm_get(&a, a.lo + i) != tm_get(&c, c.lo + i)) eq = 0;
    for (int j = 0; eq && j < 8; j++) if (tm_get(&c, c.lo + la + 1 + j) != W[j] - '0') eq = 0;
    n++;
    if (!eq && ++bad <= 5) printf("mismatch at visit %lld (steps %lld, %lld)\n", n, ka, kc);
    ra = next(&m, &a, &sa, &ka, max); rc = next(&m, &c, &sc, &kc, max);
  }
  printf("%lld visits compared, %lld mismatches; first run at step %lld, second at step %lld\n", n, bad, ka, kc);
  return bad != 0;
}
