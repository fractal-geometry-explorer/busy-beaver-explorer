// Plain (cell by cell) simulator for the block-list family, with four reports.  Shared by all 14 machines.
//
//   cc -O2 -o family family.c
//   ./family events   MACHINE STEPS   events: A turns right (A0 after a move left) with the right part
//                                     "1 (10)^n1 1 (10)^n2 1 ... (10)^nk 1 0^inf"; prints  step offset n1 ... nk
//                                     (offset = head - left end of the visited tape; n1 is the "merged" first value,
//                                     one more than the block value b1 of the round rule)
//   ./family enter    MACHINE STEPS S every entry into state S, with 30 cells either side of the head
//   ./family usage    MACHINE STEPS   how often each transition is used, final tape size
//   ./family snapshot MACHINE STEPS K [mirror]
//                                     each time the visited span grows past a multiple of K: step, state, head
//                                     offset from the leftmost 1 (or rightmost 1 with "mirror") and an FNV hash of the
//                                     tape between the outermost 1s (read right to left with "mirror"); two machines
//                                     with the same lines have the same tapes at those times
// The machine starts on a blank tape in state A, or in state S when given as MACHINE:S (for the frame-A
// conjugates of frames.py, which start in C or F).  Prints "HALT step" if it halts.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define W (1 << 27)
static unsigned char tape[W];
static int tw[6][2], td[6][2], ts[6][2];

static void parse(const char *m) {
  for (int s = 0; s < 6; s++)
    for (int y = 0; y < 2; y++) {
      const char *t = m + 7 * s + 3 * y;
      if (t[2] == '-') { ts[s][y] = -1; continue; }
      tw[s][y] = t[0] - '0'; td[s][y] = t[1] == 'R' ? 1 : -1; ts[s][y] = t[2] - 'A';
    }
}

int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage: family events|enter|usage|snapshot MACHINE STEPS [S|K [mirror]]\n"); return 2; }
  const char *mode = argv[1];
  parse(argv[2]);
  long long N = (long long)atof(argv[3]);
  int S = (argc > 4 && !strcmp(mode, "enter")) ? argv[4][0] - 'A' : -1;
  long long K = (argc > 4 && !strcmp(mode, "snapshot")) ? atoll(argv[4]) : 0, next = K;
  int mirror = argc > 5;
  long long cnt[6][2] = {{0}};
  long long pos = W / 2, lo = pos, hi = pos, t;
  int st = (strlen(argv[2]) > 42 && argv[2][41] == ':') ? argv[2][42] - 'A' : 0, lastd = 0;
  static long long vals[4096];
  for (t = 0; t < N; t++) {
    int y = tape[pos];
    cnt[st][y]++;
    if (ts[st][y] < 0) { printf("HALT %lld\n", t + 1); break; }
    int d = td[st][y];
    tape[pos] = tw[st][y];
    if (mode[0] == 'e' && mode[1] == 'v' && d == 1 && lastd == -1 && st == 0) {
      long long i = pos + 1; int ok = 1, ns = 0;
      while (1) {
        long long n = 0;
        while (tape[i] == 1 && tape[i + 1] == 0 && tape[i + 2] == 1) { n++; i += 2; }
        if (tape[i] != 1) { ok = 0; break; }
        vals[ns++] = n; i++;
        if (ns >= 4096) { ok = 0; break; }
        if (i > hi + 1) break;
        if (tape[i] == 0 && tape[i + 1] == 0) {
          int z = 1;
          for (long long j = i; j <= hi + 1; j++) if (tape[j]) { z = 0; break; }
          if (z) break;
          ok = 0; break;
        }
      }
      if (ok && (vals[0] > 1 || ns == 1)) {
        printf("%lld %lld", t + 1, pos - lo);
        for (int k = 0; k < ns; k++) printf(" %lld", vals[k]);
        printf("\n");
      }
    }
    lastd = d; pos += d; st = ts[st][y];
    if (pos < lo) lo = pos;
    if (pos > hi) hi = pos;
    if (pos <= 2 || pos >= W - 3) { fprintf(stderr, "tape too small at step %lld\n", t + 1); return 1; }
    if (S >= 0 && st == S) {
      printf("%lld from_left=%lld from_right=%lld  ", t + 1, pos - lo, hi - pos);
      for (long long j = pos - 30; j < pos + 30; j++) {
        if (j == pos) printf("[%c]", 'A' + S);
        putchar(j < lo || j > hi ? ' ' : '0' + tape[j]);
      }
      printf("\n");
    }
    if (K && hi - lo + 1 >= next) {
      unsigned long long h = 1469598103934665603ULL;
      long long a = lo, b = hi;
      while (a <= b && !tape[a]) a++;
      while (b >= a && !tape[b]) b--;
      if (mirror) for (long long i = b; i >= a; i--) { h ^= tape[i]; h *= 1099511628211ULL; }
      else for (long long i = a; i <= b; i++) { h ^= tape[i]; h *= 1099511628211ULL; }
      printf("%lld %c %lld %llx\n", t + 1, 'A' + st, mirror ? b - pos : pos - a, h);
      next += K;
    }
  }
  if (!strcmp(mode, "usage")) {
    for (int s = 0; s < 6; s++) printf("%c0:%lld %c1:%lld  ", 'A' + s, cnt[s][0], 'A' + s, cnt[s][1]);
    long long ones = 0;
    for (long long i = lo; i <= hi; i++) ones += tape[i];
    printf("\nsteps %lld ones %lld width %lld\n", t, ones, hi - lo + 1);
  }
  return 0;
}
