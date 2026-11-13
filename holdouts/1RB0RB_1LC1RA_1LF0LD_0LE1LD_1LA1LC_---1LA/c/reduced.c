/* reduced: a machine whose tape is  REST (111110)^n PREFIX  with the head at the right end, run with the block
 * of words cut short.
 *
 *   reduced MACHINE STATE PREFIX N0 TRIGGERS START [cycle]
 *
 * A *trigger* is a step at which the head visits a new cell on the right in STATE.  At a trigger the cells left of
 * the head are  REST (111110)^n PREFIX.  From trigger START on, whenever n > N0 the program deletes n - N0 words
 * and runs on.  This follows the real machine as long as crossing the block does not depend on its length, which
 * is an observation (see the README), not something this program checks: what it reports is about the reduced
 * system.  Reported: `depth record` when the head comes closer to the left end of the tape than ever since START or the last left
 * record,
 * `left record` when the left end moves, HALT, and with `cycle` a repeat of the whole reduced configuration
 * (Brent's method).  With START beyond TRIGGERS nothing is cut and the run is the real machine.
 * Build: gcc -O2 -o reduced reduced.c
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define CAP (1 << 24)
static unsigned char tape[CAP], save[CAP];
static int w[6][2], d[6][2], s[6][2];
int main(int c, char **v) {
  if (c < 7) { fprintf(stderr, "usage: reduced MACHINE STATE PREFIX N0 TRIGGERS START [cycle]\n"); return 2; }
  const char *m = v[1];
  for (int q = 0; q < 6; q++) for (int r = 0; r < 2; r++) {
    const char *p = m + 7 * q + 3 * r;
    if (p[0] == '-') { s[q][r] = -1; continue; }
    w[q][r] = p[0] - '0'; d[q][r] = p[1] == 'R' ? 1 : -1; s[q][r] = p[2] - 'A';
  }
  int S0 = v[2][0] - 'A'; const char *PF = v[3]; int PL = strlen(PF); const char *W = "011111"; int WL = 6;
  int N0 = atoi(v[4]); long long MAXT = atof(v[5]), START = atof(v[6]); int cyc = c > 7;
  long long pos = CAP / 2, lo = pos, hi = pos, mn = pos, steps = 0, trig = 0, cut = 0, depthrec = 1LL << 40;
  long long pw = 1, lam = 0, mark = 0, printed = 1; int slen = -1, sst = 0, st = 0, leftrec = 0;
  for (;;) {
    int y = tape[pos];
    if (s[st][y] < 0) {
      printf("HALT after trigger %lld (%lld steps of the reduced run, %lld words cut), head %lld cells from the left end\n",
             trig, steps, cut, pos - lo);
      return 0;
    }
    tape[pos] = w[st][y]; pos += d[st][y]; st = s[st][y]; steps++;
    if (pos < 8 || pos > CAP - 8) { printf("tape overflow\n"); return 3; }
    if (pos < mn) mn = pos;
    if (pos < lo) { lo = pos; leftrec = 1; { printf("left record after trigger %lld (step %lld of this run)\n", trig, steps); fflush(stdout); } }
    if (pos <= hi) continue;
    hi = pos;
    if (st != S0) continue;
    trig++;
    long long p = pos - 1; int ok = 1, n = 0;      /* cells read leftwards from the head: PREFIX, then words 0 1 1 1 1 1 */
    for (int j = 0; j < PL; j++) if (p - j < lo || tape[p - j] != PF[j] - '0') { ok = 0; break; }
    if (ok) {
      p -= PL;
      for (;;) {
        int g = 1;
        for (int j = 0; j < WL; j++) if (p - j < lo || tape[p - j] != W[j] - '0') { g = 0; break; }
        if (!g) break;
        p -= WL; n++;
      }
    }
    long long rest = p - lo + 1;
    if (ok && n > N0 && trig >= START) {
      long long k = (long long)(n - N0) * WL;
      memmove(tape + p + 1, tape + p + 1 + k, hi - (p + k)); memset(tape + hi - k + 1, 0, k);
      hi -= k; pos -= k; cut += n - N0; n = N0;
    }
    if (leftrec) { leftrec = 0; depthrec = 1LL << 40; }
    else if (trig > START && mn - lo < depthrec) {
      depthrec = mn - lo;
      printf("depth record %lld cells from the left end before trigger %lld (REST %lld cells)\n", depthrec, trig, rest); fflush(stdout);
    }
    mn = pos;
    if (trig == printed) { printf("trigger %lld: REST %lld cells, n = %d, %lld steps run\n", trig, rest, n, steps); fflush(stdout); printed *= 2; }
    if (cyc && ok && n == N0 && trig >= START) {
      int len = hi - lo + 1;
      if (slen == len && sst == st && !memcmp(save, tape + lo, len)) {
        printf("CYCLE: the reduced configuration of trigger %lld repeats at trigger %lld\n", mark, trig); return 0;
      }
      if (++lam == pw) { pw *= 2; lam = 0; slen = len; sst = st; mark = trig; memcpy(save, tape + lo, len); }
    }
    if (trig >= MAXT) { printf("no halt in %lld triggers (%lld steps of the reduced run)\n", trig, steps); return 0; }
  }
}
