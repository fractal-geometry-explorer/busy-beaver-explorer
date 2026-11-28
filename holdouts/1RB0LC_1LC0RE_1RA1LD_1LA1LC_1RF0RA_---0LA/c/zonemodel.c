/* zonemodel: 1RB0LC_1LC0RE_1RA1LD_1LA1LC_1RF0RA_---0LA with its body of period-10 words kept short.
 *
 *   zonemodel N0 MAXREC EVERY [check]
 *
 * A right record is a step at which the head visits a new cell on the right.  At each one the program finds the
 * longest stretch left of the head that has period 10 (the body); everything left of it is the zone.  With N0 > 0,
 * whenever the body is longer than N0+2 words, whole words are cut out of it so that N0+1 remain.  Lean's `trip`
 * (lean/Rules.lean) proves that a round trip through a body of n+1 words gives the same cells next to the zone for
 * every n, so the cut run follows the real machine as long as every trip has that form; with `check` the program
 * verifies at each right record (after the first 1,000) that the cells at the right end are those `trip` ends with,
 * and stops if not.  N0 = 0 runs the real machine.
 *
 * Prints every EVERY-th right record: record, steps of this run, zone width, a hash of the zone and state, words
 * cut so far, left records, largest zone width so far, and the step count of the real machine (this run's steps
 * plus 70 for every cut word at every right record: each round trip crosses each word twice, 70 steps in all).
 * Reports HALT, a repeat of the whole cut configuration at right records (Brent), or an exception of the check.
 * With the environment variable DUMP=r the program prints the cells of the tape at right record r (head at the
 * right end, in state B) and stops; py/trip_check.py uses it.  With CKPT=file the state is saved to that file every
 * 10 minutes (at a right record) and, if the file exists at the start, the run resumes from it.
 * Build: gcc -O3 -o zonemodel zonemodel.c        Trust level: trusted computation (our C), not a proof.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#define P 10
static const char *TM = "1RB0LC_1LC0RE_1RA1LD_1LA1LC_1RF0RA_---0LA";
static int W[6][2], D[6][2], NX[6][2];
static long mnp = 1L << 40; static long long prevnl = 0;
static void pr128(unsigned __int128 x) { char b[50]; int i = 49; b[i] = 0; do { b[--i] = '0' + (int)(x % 10); x /= 10; } while (x); printf("%s", b + i); }
int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage: zonemodel N0 MAXREC EVERY [check]\n"); return 2; }
  long N0 = atol(argv[1]); long long MAXR = atoll(argv[2]), EV = atoll(argv[3]); int chk = argc > 4;
  for (int s = 0; s < 6; s++) for (int b = 0; b < 2; b++) {
    const char *t = TM + 7 * s + 3 * b;
    if (t[2] == '-') { NX[s][b] = -1; continue; }
    W[s][b] = t[0] - '0'; D[s][b] = t[1] == 'R' ? 1 : -1; NX[s][b] = t[2] - 'A';
  }
  long SZ = 1L << 27; unsigned char *tape = calloc(SZ, 1);
  long p = SZ / 4, lo = p, hi = p; int st = 0;
  long long nr = 0, nl = 0, steps = 0, cut = 0; unsigned __int128 sumcut = 0; long maxz = 0;
  uint64_t saved = 0; long long pw = 1, lam = 0;
  const char *ck = getenv("CKPT"); time_t lastck = time(0);
  if (ck) { FILE *f = fopen(ck, "rb");
    if (f) { long w; if (fread(&p, sizeof p, 1, f) && fread(&lo, sizeof lo, 1, f) && fread(&hi, sizeof hi, 1, f) && fread(&st, sizeof st, 1, f)
              && fread(&nr, sizeof nr, 1, f) && fread(&nl, sizeof nl, 1, f) && fread(&steps, sizeof steps, 1, f) && fread(&cut, sizeof cut, 1, f)
              && fread(&sumcut, sizeof sumcut, 1, f) && fread(&maxz, sizeof maxz, 1, f) && fread(&saved, sizeof saved, 1, f)
              && fread(&pw, sizeof pw, 1, f) && fread(&lam, sizeof lam, 1, f) && fread(&w, sizeof w, 1, f) && (long)fread(tape + lo, 1, w, f) == w)
               fprintf(stderr, "resumed at right record %lld\n", nr);
             else { fprintf(stderr, "bad checkpoint\n"); return 5; }
             fclose(f); } }
  const char *TL = "111011011011", *BW = "1110110110";
  for (;;) {
    int b = tape[p];
    if (NX[st][b] < 0) { printf("HALT at right record %lld, step %lld of this run, head %ld cells from the left end\n", nr, steps, p - lo); return 0; }
    tape[p] = W[st][b]; p += D[st][b]; st = NX[st][b]; steps++;
    if (p < mnp) mnp = p;
    if (p < lo) { lo = p; nl++; if (lo < 64) { fprintf(stderr, "tape overflow on the left\n"); return 3; } }
    if (p <= hi) continue;
    hi = p; nr++; sumcut += cut;
    long j = hi - 1; while (j - P >= lo && tape[j] == tape[j - P]) j--;     /* tape[j+1 .. hi-1] has period 10 */
    long z = j - lo + 1; if (z > maxz) maxz = z;
    if (chk && nr > 1000) {
      int ok = st == 1;
      for (int x = 0; x < 12 && ok; x++) if (tape[hi - 12 + x] != TL[x] - '0') ok = 0;
      for (int c = 1; c <= 20 && ok; c++) for (int x = 0; x < 10; x++) if (tape[hi - 12 - 10 * c + x] != BW[x] - '0') ok = 0;
      if (!ok) { printf("CHECK FAILED at right record %lld\n", nr); return 4; }
    }
    if (getenv("DUMP") && nr == atoll(getenv("DUMP"))) {
      printf("DUMP %c ", 'A' + st); for (long q = lo; q < hi; q++) putchar('0' + tape[q]); putchar('\n'); return 0;
    }
    if (getenv("TRIPS") && nr > 1000) {
      if (nl == prevnl) printf("D %lld %ld %ld\n", nr, j - mnp + 1, z);
      else printf("L %lld %lld %ld\n", nr, nl - prevnl, z);
      printf("U %lld ", nr); for (long q = lo; q <= j; q++) putchar('0' + tape[q]); putchar('\n');
    }
    prevnl = nl; mnp = 1L << 40;
    long per = hi - 1 - j;
    if (N0 > 0 && per > (N0 + 2) * P) {
      long k = (per - (N0 + 1) * P) / P, del = k * P, from = j + 1 + P;     /* cells [from, from+del) go */
      memmove(tape + lo + del, tape + lo, from - lo); memset(tape + lo, 0, del); lo += del; j += del; cut += k;
    }
    if (hi > SZ - 4096) {                                                      /* move the tape back to SZ/4 */
      long w = hi - lo + 1, nlo = SZ / 4; memmove(tape + nlo, tape + lo, w); memset(tape + nlo + w, 0, SZ - (nlo + w));
      long sh = lo - nlo; p -= sh; hi -= sh; j -= sh; lo = nlo;
    }
    uint64_t H = 1469598103934665603ULL;
    for (long q = lo; q <= hi; q++) { H ^= tape[q]; H *= 1099511628211ULL; }
    H ^= (uint64_t)st * 7919;
    if (N0 > 0 && nr > 1000) {
      if (H == saved) { printf("REPEAT: the cut configuration repeats after %lld right records (at record %lld)\n", lam + 1, nr); return 0; }
      if (++lam == pw) { saved = H; pw *= 2; lam = 0; }
    }
    if (nr % EV == 0) {
      uint64_t h = 1469598103934665603ULL;
      for (long q = lo; q <= j; q++) { h ^= tape[q]; h *= 1099511628211ULL; }
      printf("%lld %lld %ld %016llx %lld %lld %ld ", nr, steps, z, (unsigned long long)(h ^ st), cut, nl, maxz);
      pr128((unsigned __int128)steps + 70 * sumcut); printf("\n"); fflush(stdout);
    }
    if (ck && time(0) - lastck >= 600) {
      char tmp[4096]; snprintf(tmp, sizeof tmp, "%s.tmp", ck); FILE *f = fopen(tmp, "wb"); long w = hi - lo + 1;
      fwrite(&p, sizeof p, 1, f); fwrite(&lo, sizeof lo, 1, f); fwrite(&hi, sizeof hi, 1, f); fwrite(&st, sizeof st, 1, f);
      fwrite(&nr, sizeof nr, 1, f); fwrite(&nl, sizeof nl, 1, f); fwrite(&steps, sizeof steps, 1, f); fwrite(&cut, sizeof cut, 1, f);
      fwrite(&sumcut, sizeof sumcut, 1, f); fwrite(&maxz, sizeof maxz, 1, f); fwrite(&saved, sizeof saved, 1, f);
      fwrite(&pw, sizeof pw, 1, f); fwrite(&lam, sizeof lam, 1, f); fwrite(&w, sizeof w, 1, f); fwrite(tape + lo, 1, w, f);
      fclose(f); rename(tmp, ck); lastck = time(0);
    }
    if (nr >= MAXR) { printf("END: no halt; largest zone %ld\n", maxz); return 0; }
  }
}
