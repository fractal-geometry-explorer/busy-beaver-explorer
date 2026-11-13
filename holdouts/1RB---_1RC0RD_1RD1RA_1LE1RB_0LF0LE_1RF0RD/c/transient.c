/* Simulate a two-symbol machine from `left S> right` (read from stdin as two 0/1 strings) until it is in a
 * post-event configuration P(d, bs) of the separator counter (state S on 0, right of the head 0^(3d+2) 1 and blank,
 * left of the head 1 1 (b 1)* 0 1 and blank).  Prints "P steps d bits(top first)" or "HALT steps" or "LIMIT steps".
 * usage: transient MACHINE S LIMIT < input        (used by py/accel.py --c) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define CAP (1 << 24)
static unsigned char tape[CAP];
static char lbuf[CAP], rbuf[CAP];
int main(int argc, char **argv) {
  const char *m = argv[1]; int S = argv[2][0] - 'A'; long long limit = atoll(argv[3]);
  int W[12], D[12], N[12], H[12];
  for (int s = 0; s < 6; s++) for (int x = 0; x < 2; x++) {
    const char *t = m + 7 * s + 3 * x; int i = 2 * s + x;
    H[i] = t[2] == '-'; if (H[i]) continue;
    W[i] = t[0] - '0'; D[i] = t[1] == 'R' ? 1 : -1; N[i] = t[2] - 'A';
  }
  if (scanf("%s %s", lbuf, rbuf) != 2) return 1;
  long ll = strlen(lbuf), rl = strlen(rbuf), base = CAP / 4;
  for (long i = 0; i < ll; i++) tape[base + i] = lbuf[i] == '1';
  for (long i = 0; i < rl; i++) tape[base + ll + i] = rbuf[i] == '1';
  long p = base + ll, hi = base + ll + rl - 1, lo = base;
  while (hi > p && !tape[hi]) hi--;
  int q = S; long long n = 0;
  long zr = 0; /* not used */ (void)zr;
  while (n < limit) {
    int x = tape[p], i = 2 * q + x;
    if (H[i]) { printf("HALT %lld\n", n); return 0; }
    if (n && q == S && x == 0 && hi > p && (hi - p) % 3 == 2 && tape[hi]) {
      long k = p + 1; while (k < hi && !tape[k]) k++;
      if (k == hi) {
        long l0 = lo; while (!tape[l0]) l0++;
        long len = p - l0; int ok = len % 2 == 0 && len >= 4 && tape[l0] && tape[l0 + 1] && !tape[p - 2] && tape[p - 1];
        for (long j = l0 + 3; ok && j < p; j += 2) if (!tape[j]) ok = 0;
        if (ok) {
          printf("P %lld %ld ", n, (hi - p - 2) / 3);
          for (long j = l0 + 2; j < p - 2; j += 2) putchar('0' + tape[j]);
          putchar('\n'); return 0;
        }
      }
    }
    tape[p] = W[i];
    if (W[i] && p > hi) hi = p;
    else if (!W[i] && p == hi) while (hi > lo && !tape[hi]) hi--;
    p += D[i]; q = N[i]; n++;
    if (p < lo) lo = p;
    if (p < 2 || p >= CAP - 2) { printf("OUT %lld\n", n); return 0; }
  }
  printf("LIMIT %lld\n", n); return 0;
}
