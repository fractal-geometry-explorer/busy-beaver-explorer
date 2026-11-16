#include "../../../tools/c/tm.h"
/* good STEPS: the condition of lean/Lockstep.lean (Good30773) on the run of 1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE.
   From step 2 on, q is the rightmost cell visited so far (cell 1 at step 2).  The head may move right from cell q
   only in state B on a 1 (then q moves two cells right, `far_B`); any other move right from q is counted as bad.
   Exit code 1 if there is one.  About 2*10^8 steps per second. */
int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: good STEPS\n"); return 2; }
  tm_machine m; tm_parse("1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE", &m);
  long long max = (long long)atof(argv[1]), k = 0, bad = 0, far = 0;
  tm_tape t; tm_tape_init(&t, 1 << 22); int st = 0;
  for (; k < 2; k++) tm_step(&m, &t, &st);
  long long q = t.hi;
  for (; k < max; k++) {
    if (t.head == q) {
      int r = tm_get(&t, q);
      if (m.s[st][r] >= 0 && m.d[st][r] == 1) {
        if (st == 1 && r == 1) { far++; q += 2; }
        else if (++bad <= 10) printf("bad: step %lld, state %c reads %d on cell q\n", k, 'A' + st, r);
      }
    }
    if (!tm_step(&m, &t, &st)) { printf("halts after %lld steps\n", k + 1); break; }
  }
  printf("%lld steps, %lld moves right from q in state B on a 1, %lld other moves right from q (bad), q = %lld\n",
         k, far, bad, q);
  return bad != 0;
}
