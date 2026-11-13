// xdump M STEPS [from]: print the tape at every step where the head is in state A on a 0 and the 18 cells to its
// left read i e x i 1 (i = 11000, e = 110, x = 1000 or 1100): "EV index step pos tape-with-|"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1 << 24)
static unsigned char tape[N];
int main(int argc, char **argv) {
  char *m = argv[1]; int nw[6][2], mv[6][2], ns[6][2];
  for (int s = 0; s < 6; s++) for (int r = 0; r < 2; r++) {
    char *p = m + s * 7 + r * 3;
    if (p[2] == '-') { ns[s][r] = -1; continue; }
    nw[s][r] = p[0] - '0'; mv[s][r] = p[1] == 'R' ? 1 : -1; ns[s][r] = p[2] - 'A';
  }
  long long T = atoll(argv[2]), from = argc > 3 ? atoll(argv[3]) : 0;
  const char *pat = "110001101x0011000"; /* i e x(1 x 0 0) i, then the 1 of d */
  long pos = N / 2, lo = pos, hi = pos; int st = 0; long long cnt = 0;
  for (long long t = 0; t < T; t++) {
    int r = tape[pos]; int s2 = ns[st][r];
    if (s2 < 0) { printf("HALT %lld\n", t + 1); return 0; }
    if (st == 0 && r == 0 && tape[pos - 1] == 1) {
      int ok = 1; long q = pos - 18;
      for (int j = 0; j < 17 && ok; j++) if (pat[j] != 'x' && tape[q + j] != pat[j] - '0') ok = 0;
      if (ok) { cnt++; if (t >= from) { printf("EV %lld %lld %ld ", cnt, t, pos - N / 2);
        for (long i = lo; i <= hi; i++) { if (i == pos) putchar('|'); putchar('0' + tape[i]); } putchar('\n'); } }
    }
    tape[pos] = nw[st][r]; pos += mv[st][r]; st = s2;
    if (pos < lo) lo = pos; if (pos > hi) hi = pos;
  }
  return 0;
}
