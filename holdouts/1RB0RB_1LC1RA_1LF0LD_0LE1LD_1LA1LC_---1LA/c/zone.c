/* zone: the leftmost zone of a machine of the `111110` family, run alone.
 *
 *   zone MACHINE PASS STATE PREFIX T0 TICKS [quiet]
 *
 * Runs MACHINE from blank tape to its T0-th trigger (a new cell on the right in STATE, the tape then being
 * REST (111110)^n PREFIX).  From there it keeps only REST and repeats a *tick*: the tape is set to
 * REST (111110)^12 with the head on the last 0 in state PASS (a pass that has just crossed the block, see
 * `cross_left`), and the machine runs until the head leaves this stretch on the right.  The cells left of the
 * words that are then at the right end are the new REST.  This is what the leftmost zone of the real machine goes
 * through if every visit is one such pass and what the sweep back does to the cells further right does not come
 * back to it; that is an observation (see the README), and what is reported here is about this model.
 * Reported: `arrival` when a pass reaches the left end of the tape (the block lengths of REST before and after,
 * -k for k zeros), `depth` records between arrivals unless `quiet`, HALT, and CYCLE when REST repeats (Brent).
 * Build: gcc -O2 -o zone zone.c
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define CAP (1 << 22)
#define PAD (1 << 20)
#ifndef MW
#define MW 12
#endif
static unsigned char tape[CAP], save[1 << 16];
static int w[6][2], d[6][2], s[6][2];
static void blocks(const unsigned char *c, long long n) {
  for (long long p = 0; p < n;) {
    long long q = p; while (q < n && c[q] == c[p]) q++;
    if (c[p]) printf(" %lld", q - p); else if (q - p > 1) printf(" -%lld", q - p);
    p = q;
  }
  printf("\n");
}
int main(int c, char **v) {
  if (c < 7) { fprintf(stderr, "usage: zone MACHINE PASS STATE PREFIX T0 TICKS [quiet]\n"); return 2; }
  const char *m = v[1];
  for (int q = 0; q < 6; q++) for (int r = 0; r < 2; r++) {
    const char *p = m + 7 * q + 3 * r;
    if (p[0] == '-') { s[q][r] = -1; continue; }
    w[q][r] = p[0] - '0'; d[q][r] = p[1] == 'R' ? 1 : -1; s[q][r] = p[2] - 'A';
  }
  int P = v[2][0] - 'A', S0 = v[3][0] - 'A'; const char *PF = v[4]; int PL = strlen(PF);
  long long T0 = atof(v[5]), TICKS = atof(v[6]); int quiet = c > 7;
  static const unsigned char WORD[6] = {1, 1, 1, 1, 1, 0};
  long long pos = PAD, lo = pos, hi = pos, trig = 0; int st = 0;
  while (trig < T0) {                              /* the real machine up to trigger T0 */
    int y = tape[pos];
    if (s[st][y] < 0) { printf("HALT before trigger %lld\n", T0); return 0; }
    tape[pos] = w[st][y]; pos += d[st][y]; st = s[st][y];
    if (pos < lo) lo = pos;
    if (pos > hi) { hi = pos; if (st == S0) trig++; }
    if (pos < 8 || pos > CAP - 8) { printf("tape overflow\n"); return 3; }
  }
  long long p = pos - 1 - PL;
  for (int j = 0; j < PL; j++) if (tape[p + 1 + j] != PF[j] - '0') { printf("no PREFIX at trigger %lld\n", T0); return 3; }
  long long n = 0; while (p - 5 >= lo && !memcmp(tape + p - 5, WORD, 6)) { p -= 6; n++; }
  while (lo < p && !tape[lo]) lo++;
  long long len = p - lo + 1;                      /* REST = tape[lo .. p] */
  memset(tape + p + 1, 0, hi - p + 8);
  printf("trigger %lld: REST %lld cells before %lld words:", T0, len, n); blocks(tape + lo, len);
  long long pw = 1, lam = 0, mark = 0, slen = -1, steps = 0, deep = 1LL << 40, arrivals = 0;
  for (long long k = 1; k <= TICKS; k++) {
    long long E = lo + len + 6 * MW - 1;
    for (int j = 0; j < MW; j++) memcpy(tape + lo + len + 6 * j, WORD, 6);
    memset(tape + E + 1, 0, 16);
    long long mn = E, lo0 = lo; pos = E; st = P;
    static unsigned char before[1 << 16]; long long blen = len; if (len < (1 << 16)) memcpy(before, tape + lo, len);
    for (;;) {
      int y = tape[pos];
      if (s[st][y] < 0) {
        printf("HALT in tick %lld (%lld steps of the model, %lld arrivals before): REST was", k, steps, arrivals);
        blocks(before, blen); return 0;
      }
      tape[pos] = w[st][y]; pos += d[st][y]; st = s[st][y]; steps++;
      if (pos < mn) mn = pos;
      if (pos > E) break;
      if (pos < 8) { printf("tape overflow on the left\n"); return 3; }
    }
    while (lo > 8 && (tape[lo - 1] || tape[lo - 2] || tape[lo - 3])) lo--;
    while (lo < E && !tape[lo]) lo++;
    int o, found = 0; long long q = 0;
    for (o = 0; o < 12 && !found; o++) {
      long long j = 0; q = E - o;
      while (q - 5 >= lo && !memcmp(tape + q - 5, WORD, 6)) { q -= 6; j++; }
      if (j >= MW - 4) found = 1;
    }
    if (!found) { printf("tick %lld: no block of words at the right end afterwards (state %c)\n", k, 'A' + st); blocks(tape + lo, E - lo + 9); return 0; }
    len = q - lo + 1;
    memset(tape + q + 1, 0, E + 16 - q);
    if (mn <= lo0 + 1 || lo != lo0) {
      arrivals++;
      printf("arrival %lld in tick %lld (left end moved %lld cells, head leaves in state %c)\n  before:", arrivals, k, lo0 - lo, 'A' + st);
      blocks(before, blen); printf("  after: "); blocks(tape + lo, len); fflush(stdout);
      deep = 1LL << 40;
    } else if (mn - lo < deep) {
      deep = mn - lo;
      if (!quiet) { printf("depth %lld cells from the left end in tick %lld (REST %lld cells)\n", deep, k, len); fflush(stdout); }
    }
    if (len < (1 << 16)) {
      if (slen == len && !memcmp(save, tape + lo, len)) { printf("CYCLE: REST after tick %lld is REST after tick %lld\n", k, mark); return 0; }
      if (++lam == pw) { pw *= 2; lam = 0; slen = len; mark = k; memcpy(save, tape + lo, len); }
    }
  }
  printf("no halt in %lld ticks (%lld steps of the model, %lld arrivals); REST %lld cells:", TICKS, steps, arrivals, len); blocks(tape + lo, len);
  return 0;
}
