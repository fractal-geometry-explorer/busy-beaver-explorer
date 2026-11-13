// Block-crossing simulator for 1RB0RC_1LA0LD_1RB0RD_1LE0RF_0LB0RB_1RC--- (bbchallenge 32641).
// It runs the machine from blank tape and proposes the data that the Coq proof checks:
//   the macro configurations at chosen moments and the list of (state, side, block) keys that were looked up.
// usage: macro37 K J T t1 t2 ...
//   K  block size (<= 59);  J  length of the short first block left of the origin (0 <= J < K)
//   T  the run stops at step T, which must be a block crossing (the configuration there is dumped last);
//   ti a configuration is dumped at the first block crossing at or after step ti.
// The blocks are [K i, K i + K) for i >= 0, then [-J, 0), then [-J - K (i+1), -J - K i) for i >= 0.
// A block is written as the number 2^len + sum cell_i 2^i, cell_0 being the cell nearest to the head.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#define N (1 << 22)
#define O (N / 2)
static unsigned char tape[N];
#define HB 22
static uint64_t hk[1 << HB]; static unsigned char hu[1 << HB];
static int K, J;
static void blk(long pos, long *s, int *len) {
  if (pos >= 0) { *s = pos / K * K; *len = K; }
  else if (pos >= -J) { *s = -J; *len = J; }
  else { long d = (-J - 1 - pos) / K; *s = -J - K * (d + 1); *len = K; }
}
static uint64_t valR(long s, int len) { uint64_t v = 1; for (int i = len - 1; i >= 0; i--) v = v * 2 + tape[O + s + i]; return v; }
static uint64_t valL(long s, int len) { uint64_t v = 1; for (int i = 0; i < len; i++) v = v * 2 + tape[O + s + i]; return v; }
static void dump(long long cross, long long t, long pos, int q, int f, long lo, long hi) {
  printf("CFG %lld %lld %ld %c %d\nL", cross, t, pos, 'A' + q, f);
  long p = f ? pos - 1 : pos; long s; int len;
  while (p >= lo) { blk(p, &s, &len); printf(" %llu", (unsigned long long)valL(s, len)); p = s - 1; }
  printf("\nR");
  p = f ? pos : pos + 1;
  while (p <= hi) { blk(p, &s, &len); printf(" %llu", (unsigned long long)valR(s, len)); p = s + len; }
  printf("\n");
}
int main(int argc, char **argv) {
  K = atoi(argv[1]); J = atoi(argv[2]); long long T = atoll(argv[3]);
  int nt = argc - 4, it = 0;
  int W[6][2] = {{1,0},{1,0},{1,0},{1,0},{0,0},{1,-1}};
  int D[6][2] = {{1,1},{-1,-1},{1,1},{-1,1},{-1,1},{1,0}};
  int Q[6][2] = {{1,2},{0,3},{1,3},{4,5},{1,1},{2,-1}};
  long pos = 0, lo = J > 0 ? -J : 0, hi = -1; int q = 0, f = 1; long long t = 0, cross = 0; int maxin = 0;
  for (;;) {
    while (it < nt && t >= atoll(argv[4 + it])) { dump(cross, t, pos, q, f, lo, hi); it++; }
    if (t == T) { dump(cross, t, pos, q, f, lo, hi); break; }
    long s; int len; blk(pos, &s, &len);
    uint64_t key = (f ? valR(s, len) : valL(s, len)) * 16 + q * 2 + f;
    uint64_t h = (key * 0x9E3779B97F4A7C15ULL) >> (64 - HB);
    while (hu[h] && hk[h] != key) h = (h + 1) & ((1 << HB) - 1);
    if (!hu[h]) { hu[h] = 1; hk[h] = key; }
    long old = pos; int in = 0;
    while (pos >= s && pos < s + len) {
      if (t == T) { printf("NOTCROSS %ld %c\n", pos, 'A' + q); return 1; }
      int c = tape[O + pos]; if (Q[q][c] < 0) { printf("HALT\n"); return 1; }
      tape[O + pos] = W[q][c]; old = pos; pos += D[q][c]; q = Q[q][c]; t++; in++;
    }
    if (in > maxin) maxin = in;
    if (s < lo) lo = s;
    if (s + len - 1 > hi) hi = s + len - 1;
    f = pos > old; cross++;
  }
  for (long i = 0; i < (1 << HB); i++) if (hu[i]) printf("KEY %c %d %llu\n", 'A' + (int)(hk[i] % 16 / 2), (int)(hk[i] % 2), (unsigned long long)(hk[i] / 16));
  printf("MAXIN %d\n", maxin);
  return 0;
}
