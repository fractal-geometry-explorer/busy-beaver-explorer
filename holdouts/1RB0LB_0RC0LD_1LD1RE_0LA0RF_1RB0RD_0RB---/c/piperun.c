// piperun.c: the word pass of c/deficit.c (deficit form, lean/Deficit.lean) with several rounds in flight at once.
//
// A round only moves right and only touches the 5 cells at its position, and round r+1 starts 2 cells left of
// round r.  So round r+1 can run behind round r as long as it stays at least 8 cells behind it: THREADS threads
// take rounds in turn, each waiting on the position of the round before.  The rounds, and so the words, are exactly
// those of c/deficit.c and c/wordrun.c (check with DUMP: the files must be equal).
//
// usage: gcc -O2 -pthread -o piperun piperun.c && ./piperun THREADS ROUNDS [EVERY [DUMP [START R0]]]
//   START R0: go on from START, a DUMP of the word after R0 rounds
// stdout: JUNK (the pass ends on a 0 with a 1 right after it), 1011, 111 (with HALT for 1111 and STOP for 11100,
//   which has no proved rule), positions counted from the front of the word of that round, with the cells from
//   4 before the position to 24 after it (further left the rounds behind may already have changed them).  For a
//   JUNK line, shown cells 2 to 4 are the digit block the round wrote just before the junk: 100 means it took 3
//   visits, the dangerous case (see README); 000 means 2 visits, safe.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <limits.h>
#include <pthread.h>
static uint8_t *T; static const long N = 1L << 30; static long F0;
static long R, every, NT, R0;
#define SLOTS 64
static long prog[SLOTS];     // position of round r in slot r % SLOTS (LONG_MAX when done)
static long tag[SLOTS];      // which round the slot holds
static long Emax, stopr = LONG_MAX, njunk, n1011;
static pthread_mutex_t mu = PTHREAD_MUTEX_INITIALIZER;
static void show(long a, long b) { putchar('|'); for (long i = a; i < b; i++) putchar('0' + T[i]); putchar('|'); }
static void event(const char *what, long r, long p, long F, long e, long c) {
  if (r > __atomic_load_n(&stopr, __ATOMIC_ACQUIRE)) return;   // a round behind a stopped one
  pthread_mutex_lock(&mu);
  printf("%s round %ld at %ld from the front, level %ld deficit %ld ", what, r, p - F, e, c);
  show(p - 4, p + 24); printf("\n"); fflush(stdout);   // cells left of p - 4 may already hold later rounds
  pthread_mutex_unlock(&mu);
}
static void *worker(void *arg) {
  long t = (long)arg;
  for (long r = R0 + t + 1; r <= R; r += NT) {
    long s = r % SLOTS;
    // wait until round r - 1 has started
    while (__atomic_load_n(&tag[s], __ATOMIC_ACQUIRE) != r) ;
    long ps = (r - 1) % SLOTS;
    long F = F0 - 2 * r;
    if (__atomic_load_n(&stopr, __ATOMIC_ACQUIRE) < r) { __atomic_store_n(&prog[s], LONG_MAX, __ATOMIC_RELEASE); break; }
    T[F] = 1; T[F + 1] = 0;
    __atomic_store_n(&prog[s], F, __ATOMIC_RELEASE);
    {  // round r + 1 may start now, behind this one (its slot's earlier round, r + 1 - SLOTS, is long done)
      long n = (r + 1) % SLOTS;
      __atomic_store_n(&prog[n], LONG_MIN, __ATOMIC_RELAXED);
      __atomic_store_n(&tag[n], r + 1, __ATOMIC_RELEASE);
    }
    long p = F, e = 0, c = 0, q = r == R0 + 1 ? LONG_MAX : __atomic_load_n(&prog[ps], __ATOMIC_ACQUIRE);
    for (;;) {
      if (e < 62 && c == (1L << e)) break;
      while (q < p + 8) q = __atomic_load_n(&prog[ps], __ATOMIC_ACQUIRE);
      uint8_t *w = T + p;
      if (w[0] == 0) {
        w[0] = 1; c++;
        if (e < 62 && c == (1L << e) && w[1] == 1) { __atomic_add_fetch(&njunk, 1, __ATOMIC_RELAXED); event("JUNK", r, p, F, e, c - 1); }
        continue;
      }
      if (w[2] == 0) { w[0] = e == 0 ? 0 : !(c & 1); w[1] = 0; if (e > 0) { e--; c /= 2; } p += 3; }
      else if (w[1] == 0 && w[3] == 0) { e++; c *= 2; p += 4; }
      else if (w[1] == 0) {
        __atomic_add_fetch(&n1011, 1, __ATOMIC_RELAXED); event("1011", r, p, F, e, c);
        w[0] = 0; w[2] = 0; w[3] = 1; c++;
        if (e < 62 && c == (1L << e) && w[4] == 1) { __atomic_add_fetch(&njunk, 1, __ATOMIC_RELAXED); event("JUNK(after 1011)", r, p + 3, F, e, c - 1); }
      } else {
        event("111", r, p, F, e, c);
        pthread_mutex_lock(&mu);
        if (w[3] == 1) printf("HALT round %ld (1111)\n", r); else if (w[4] == 0) printf("STOP round %ld: 11100 has no proved rule\n", r);
        pthread_mutex_unlock(&mu);
        if (w[3] == 1 || w[4] == 0) { __atomic_store_n(&stopr, r, __ATOMIC_RELEASE); break; }
        w[1] = 0; c++;
      }
      if (c > (1L << 40)) { fprintf(stderr, "deficit too large\n"); exit(1); }
      if (p + 8 >= N) { fprintf(stderr, "tape overflow\n"); exit(1); }
      __atomic_store_n(&prog[s], p, __ATOMIC_RELEASE);
    }
    pthread_mutex_lock(&mu); if (p + 4 > Emax) Emax = p + 4; pthread_mutex_unlock(&mu);
    __atomic_store_n(&prog[s], LONG_MAX, __ATOMIC_RELEASE);
    if (r % every == 0) { pthread_mutex_lock(&mu); fprintf(stderr, "round %ld junk %ld 1011 %ld\n", r, njunk, n1011); pthread_mutex_unlock(&mu); }
    if (__atomic_load_n(&stopr, __ATOMIC_ACQUIRE) <= r) break;
  }
  return NULL;
}
int main(int argc, char **argv) {
  setvbuf(stdout, NULL, _IOLBF, 0);
  if (argc < 3) { fprintf(stderr, "usage: %s THREADS ROUNDS [EVERY [DUMP]]\n", argv[0]); return 2; }
  NT = atol(argv[1]); R = atol(argv[2]); every = argc > 3 ? atol(argv[3]) : 10000;
  T = calloc(N, 1); F0 = N / 4; T[F0] = 1; Emax = F0 + 1;   // after 0 rounds the word is 1
  if (argc > 6) {  // resume: START is a DUMP of the word after R0 rounds
    R0 = atol(argv[6]); F0 = N / 4 + 2 * R0; T[F0] = 0;
    FILE *f = fopen(argv[5], "r"); if (!f) { perror(argv[5]); return 1; }
    long i = F0 - 2 * R0; int ch; while ((ch = fgetc(f)) == '0' || ch == '1') T[i++] = ch - '0';
    fclose(f); Emax = i;
  }
  tag[(R0 + 1) % SLOTS] = R0 + 1; prog[(R0 + 1) % SLOTS] = LONG_MIN;
  pthread_t th[64];
  for (long t = 0; t < NT; t++) pthread_create(&th[t], NULL, worker, (void *)t);
  for (long t = 0; t < NT; t++) pthread_join(th[t], NULL);
  long last = stopr < R ? stopr : R, F = F0 - 2 * last, E = Emax;
  while (E > F && T[E - 1] == 0) E--;
  printf("DONE %ld rounds, length %ld, junk %ld, 1011 %ld\n", last, E - F, njunk, n1011);
  if (argc > 4) { FILE *f = fopen(argv[4], "w"); for (long i = F; i < E; i++) fputc('0' + T[i], f); fputc('\n', f); fclose(f); }
  return 0;
}
