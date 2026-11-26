// Which configurations of 1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC halt within LIMIT steps (plain simulation).
// stdin: lines "LEFT STATE RIGHT" (cells left of the head; the state; the head cell and the cells right of it;
// "-" for none).  stdout: "HALT steps LEFT STATE RIGHT" for each one that halts, then a count.  Used by py/failhalt.py.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define T (1 << 20)
static unsigned char tape[T];
static const int W_[6][2] = {{1, 1}, {1, 1}, {1, 1}, {0, 0}, {0, -1}, {1, 0}};
static const int D_[6][2] = {{1, -1}, {-1, 1}, {1, -1}, {1, 1}, {1, 0}, {1, -1}};
static const int Q_[6][2] = {{1, 5}, {2, 3}, {0, 0}, {0, 4}, {2, -1}, {5, 2}};
int main(int argc, char **argv) {
  long limit = atol(argv[1]), n = 0, h = 0, oob = 0;
  static char l[1 << 16], r[1 << 16], qs[8];
  while (scanf("%65535s %7s %65535s", l, qs, r) == 3) {
    memset(tape, 0, T);
    int pos = T / 2, L = strcmp(l, "-") ? strlen(l) : 0, R = strcmp(r, "-") ? strlen(r) : 0;
    for (int i = 0; i < L; i++) tape[pos - L + i] = l[i] - '0';
    for (int i = 0; i < R; i++) tape[pos + i] = r[i] - '0';
    int q = qs[0] - 'A', res = 0;
    long t = 0;
    while (t < limit) {
      int s = tape[pos];
      if (Q_[q][s] < 0) { res = 1; break; }
      tape[pos] = W_[q][s]; pos += D_[q][s]; q = Q_[q][s]; t++;
      if (pos < 4 || pos > T - 4) { res = 2; break; }
    }
    n++;
    if (res == 1) { h++; printf("HALT %ld %s %s %s\n", t, l, qs, r); }
    if (res == 2) oob++;
  }
  printf("runs %ld halts %ld out-of-tape %ld\n", n, h, oob);
  return 0;
}
