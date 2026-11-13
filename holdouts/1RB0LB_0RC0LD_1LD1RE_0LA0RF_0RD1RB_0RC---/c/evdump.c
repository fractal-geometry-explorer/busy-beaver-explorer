// evdump M P S STEPS: run M from blank tape; at every step where the head is in state S on cell P (cells counted
// from the start cell) print "EV <index> <step> <tape lo..hi with | before the head cell>".
#include <stdio.h>
#include <stdlib.h>
#define N (1 << 24)
static unsigned char tape[N];
int main(int argc, char **argv) {
  if (argc < 5) { fprintf(stderr, "usage: evdump M P S STEPS\n"); return 1; }
  char *m = argv[1]; int nw[6][2], mv[6][2], ns[6][2];
  for (int s = 0; s < 6; s++) for (int r = 0; r < 2; r++) {
    char *p = m + s * 7 + r * 3;
    if (p[2] == '-') { ns[s][r] = -1; continue; }
    nw[s][r] = p[0] - '0'; mv[s][r] = p[1] == 'R' ? 1 : -1; ns[s][r] = p[2] - 'A';
  }
  long P = atol(argv[2]); int S = argv[3][0] - 'A'; long long T = atoll(argv[4]);
  long pos = N / 2, lo = pos, hi = pos; int st = 0; long long cnt = 0;
  for (long long t = 0; t < T; t++) {
    int r = tape[pos]; int s2 = ns[st][r];
    if (s2 < 0) { printf("HALT %lld\n", t + 1); return 0; }
    if (st == S && pos - N / 2 == P) {
      printf("EV %lld %lld ", ++cnt, t);
      for (long i = lo; i <= hi; i++) { if (i == pos) putchar('|'); putchar('0' + tape[i]); }
      if (pos > hi) putchar('|');
      putchar('\n');
    }
    tape[pos] = nw[st][r]; pos += mv[st][r]; st = s2;
    if (pos < lo) lo = pos; if (pos > hi) hi = pos;
    if (pos <= 0 || pos >= N - 1) { fprintf(stderr, "tape full\n"); return 2; }
  }
  return 0;
}
