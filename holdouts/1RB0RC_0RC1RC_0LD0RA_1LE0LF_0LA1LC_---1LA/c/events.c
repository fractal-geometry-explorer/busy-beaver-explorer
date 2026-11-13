// events: plain simulation of a 2-symbol machine from blank tape; prints one line per *event* (the head moves left, in
// state E, onto the leftmost visited cell or beyond it):  steps  ones  width  crc32
// where ones/width/crc32 describe the tape from its first 1 to its last 1 (crc32 of the cells as ASCII '0'/'1', the
// same value as Python's zlib.crc32).  usage: events MACHINE MAXSTEPS
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int nw[6][2], mv[6][2], ns[6][2];
#define N (1 << 26)
static unsigned char tape[N];
static uint32_t tab[256];
int main(int c, char **v) {
  if (c < 3) { fprintf(stderr, "usage: events MACHINE MAXSTEPS\n"); return 1; }
  char *m = v[1]; long long max = atoll(v[2]);
  for (int s = 0; s < 6; s++) for (int r = 0; r < 2; r++) {
    char *t = m + 7 * s + 3 * r;
    if (t[2] == '-') { ns[s][r] = -1; continue; }
    nw[s][r] = t[0] - '0'; mv[s][r] = t[1] == 'R' ? 1 : -1; ns[s][r] = t[2] - 'A';
  }
  for (uint32_t i = 0; i < 256; i++) { uint32_t x = i; for (int k = 0; k < 8; k++) x = x & 1 ? 0xEDB88320u ^ (x >> 1) : x >> 1; tab[i] = x; }
  int p = N / 2, lo = p, hi = p, st = 0;
  for (long long k = 1; k <= max; k++) {
    int r = tape[p], t = ns[st][r];
    if (t < 0) { printf("HALT %lld\n", k); return 0; }
    int left = mv[st][r] < 0;
    tape[p] = nw[st][r]; p += mv[st][r]; st = t;
    if (p > hi) hi = p;
    if (left && p <= lo) {
      lo = p;
      if (st == 4) {
        int a = lo, b = hi; while (a <= b && !tape[a]) a++; while (b >= a && !tape[b]) b--;
        uint32_t crc = 0xFFFFFFFFu; long ones = 0;
        for (int i = a; i <= b; i++) { ones += tape[i]; crc = tab[(crc ^ ('0' + tape[i])) & 255] ^ (crc >> 8); }
        printf("%lld %ld %d %u\n", k, ones, b - a + 1, crc ^ 0xFFFFFFFFu);
      }
      if (lo < 10 || hi > N - 10) { printf("OUT\n"); return 0; }
    }
  }
  return 0;
}
