/* blocks.c: run a machine from blank tape; each time the head extends the tape on SIDE (L or R) in state STATE,
   print the step and the tape as a list of blocks of 1s split at runs of at least SEP zeros, run-length encoded
   from the far end: "len x count".  Gaps of fewer than SEP zeros stay inside a block (shown as a word).
   usage: gcc -O2 -I tools/c -o blocks blocks.c && ./blocks MACHINE MAX SIDE STATE SEP [MINGAP]
   MINGAP: print only events at least that many steps after the previous one (default 0). */
#include "tm.h"
static void show(const tm_tape *t, int sep, int fromright) {
  long long a = t->lo, b = t->hi;
  while (a <= b && !tm_get(t, a)) a++;
  while (b >= a && !tm_get(t, b)) b--;
  char *s = malloc(b - a + 2); long long n = 0;
  if (fromright) for (long long p = b; p >= a; p--) s[n++] = '0' + tm_get(t, p);
  else for (long long p = a; p <= b; p++) s[n++] = '0' + tm_get(t, p);
  s[n] = 0;
  long long i = 0; char prev[4096] = ""; long long cnt = 0;
  while (i < n) {
    long long j = i, z;
    for (;;) { while (j < n && s[j] == '1') j++; z = j; while (z < n && s[z] == '0') z++; if (z >= n || z - j >= sep) break; j = z; }
    char cur[4096]; long long L = j - i; int ones = 1;
    for (long long q = i; q < j; q++) if (s[q] != '1') ones = 0;
    if (ones) snprintf(cur, sizeof cur, "%lld", L);
    else if (L < 4000) { memcpy(cur, s + i, L); cur[L] = 0; } else snprintf(cur, sizeof cur, "?%lld", L);
    if (cnt && !strcmp(cur, prev)) cnt++;
    else { if (cnt) printf(cnt > 1 ? " %sx%lld" : " %s", prev, cnt); strcpy(prev, cur); cnt = 1; }
    i = z;
  }
  if (cnt) printf(cnt > 1 ? " %sx%lld" : " %s", prev, cnt);
  printf("\n"); free(s);
}
int main(int argc, char **argv) {
  if (argc < 6) { fprintf(stderr, "usage: blocks MACHINE MAX SIDE STATE SEP [MINGAP]\n"); return 2; }
  tm_machine m; tm_parse(argv[1], &m); long long max = atoll(argv[2]); int right = argv[3][0] == 'R';
  int want = argv[4][0] - 'A', sep = atoi(argv[5]); long long mingap = argc > 6 ? atoll(argv[6]) : 0, last = -mingap - 1;
  tm_tape t; tm_tape_init(&t, 1 << 16); int st = 0;
  for (long long k = 1; k <= max; k++) {
    long long lo = t.lo, hi = t.hi;
    if (!tm_step(&m, &t, &st)) { printf("HALT %lld\n", k); return 0; }
    if (st == want && (right ? t.head > hi : t.head < lo) && k - last > mingap) { printf("%lld", k); show(&t, sep, !right); last = k; }
  }
  return 0;
}
