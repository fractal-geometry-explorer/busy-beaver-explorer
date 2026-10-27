/* For each line "id c q0modq1 q1 nlo" (q1 < 2^62), print every n in [nlo, N) with c 2^n = q0 (mod q1). */
#include <stdio.h>
#include <stdlib.h>
typedef unsigned __int128 u128;
int main(int argc, char **argv) {
  long N = argc > 1 ? atol(argv[1]) : 4096;
  long id; unsigned long long c, r, q, nlo; long lines = 0, hits = 0;
  while (scanf("%ld %llu %llu %llu %llu", &id, &c, &r, &q, &nlo) == 5) {
    lines++;
    u128 pw = c % q;
    for (long n = 0; n < N; n++) {
      if (n >= (long)nlo && pw == r) { printf("HIT %ld %ld\n", id, n); hits++; }
      pw = (pw * 2) % q;
    }
  }
  fprintf(stderr, "lines %ld hits %ld up to n < %ld\n", lines, hits, N);
  return 0;
}
