/* tapehash.c: run a machine from blank tape and print, at each step count given, the state and the FNV-1a hash
   of the tape between its outermost 1s (as py/accel.py --hash prints it), to check the accelerated simulator.
   usage: gcc -O2 -I tools/c -o tapehash tapehash.c && ./tapehash MACHINE S1 S2 ...   (increasing) */
#include "tm.h"
int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: tapehash MACHINE S1 S2 ...\n"); return 2; }
  tm_machine m; tm_parse(argv[1], &m); tm_tape t; tm_tape_init(&t, 1 << 22); int st = 0; long long k = 0;
  for (int a = 2; a < argc; a++) {
    long long T = (long long)atof(argv[a]);
    while (k < T) { k++; if (!tm_step(&m, &t, &st)) { printf("HALT %lld\n", k); return 0; } }
    long long lo = t.lo, hi = t.hi;
    while (lo <= hi && !tm_get(&t, lo)) lo++;
    while (hi >= lo && !tm_get(&t, hi)) hi--;
    unsigned long long h = 0xcbf29ce484222325ULL;
    for (long long p = lo; p <= hi; p++) { h ^= (unsigned long long)(48 + tm_get(&t, p)); h *= 0x100000001b3ULL; }
    printf("hash %lld %c %016llx %lld\n", k, 'A' + st, h, hi - lo + 1);
  }
  return 0;
}
