/* Sampled hashes of a run's configurations, without the state: for finding runs whose tapes meet later.

   usage: cfghash MACHINE STEPS MOD

   The tape is hashed relative to the head, H = sum of B^(i - head) over the cells i holding a 1, modulo 2^61 - 1, and
   its mirror image G = sum of B^(head - i); both are updated in O(1) per step.  A configuration is printed ("F H step"
   or "M G step") when its hash is divisible by MOD.  Since the choice depends only on the tape and the head, two runs
   that reach the same tapes print the same hashes from then on, whatever their states and step counts; comparing
   one machine's F lines with another's F lines (or M lines, for a mirror image) finds them.  A halt or a run off the
   tape array is reported on stderr. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#define T (1 << 27)
typedef unsigned __int128 u128;
static const uint64_t P = (1ULL << 61) - 1;

static uint64_t mulm(uint64_t a, uint64_t b) {
  u128 r = (u128)a * b;
  uint64_t s = (uint64_t)(r & P) + (uint64_t)(r >> 61);
  return s >= P ? s - P : s;
}

static uint64_t powm(uint64_t a, uint64_t e) {
  uint64_t r = 1;
  while (e) {
    if (e & 1) r = mulm(r, a);
    a = mulm(a, a);
    e >>= 1;
  }
  return r;
}

static unsigned char tape[T];

int main(int argc, char **argv) {
  if (argc < 4) {
    fprintf(stderr, "usage: cfghash MACHINE STEPS MOD\n");
    return 2;
  }
  const char *m = argv[1];
  long long N = atoll(argv[2]);
  uint64_t MOD = strtoull(argv[3], NULL, 10);
  int w[6][2], d[6][2], nx[6][2], ns = 0;
  for (const char *p = m; *p; p++) ns += *p == '_';
  ns += 1;
  for (int s = 0; s < 6; s++)
    for (int b = 0; b < 2; b++) {
      nx[s][b] = -1;
      if (s >= ns) continue;
      const char *p = m + 7 * s + 3 * b;
      if (p[0] == '-') continue;
      w[s][b] = p[0] - '0';
      d[s][b] = p[1] == 'R' ? 1 : -1;
      nx[s][b] = p[2] - 'A';
    }
  uint64_t B = 1000003, Bi = powm(B, P - 2), H = 0, G = 0;
  long long h = T / 2;
  int s = 0;
  for (long long i = 0; i < N; i++) {
    if (H % MOD == 0) printf("F %llu %lld\n", (unsigned long long)H, i);
    if (G % MOD == 0) printf("M %llu %lld\n", (unsigned long long)G, i);
    int b = tape[h];
    if (nx[s][b] < 0) {
      fprintf(stderr, "halt %lld\n", i);
      break;
    }
    int nw = w[s][b];
    if (nw != b) {
      H = nw ? (H + 1) % P : (H + P - 1) % P;
      G = nw ? (G + 1) % P : (G + P - 1) % P;
    }
    tape[h] = (unsigned char)nw;
    if (d[s][b] > 0) {
      h++;
      H = mulm(H, Bi);
      G = mulm(G, B);
    } else {
      h--;
      H = mulm(H, B);
      G = mulm(G, Bi);
    }
    s = nx[s][b];
    if (h < 2 || h > T - 3) {
      fprintf(stderr, "out %lld\n", i);
      break;
    }
  }
  return 0;
}
