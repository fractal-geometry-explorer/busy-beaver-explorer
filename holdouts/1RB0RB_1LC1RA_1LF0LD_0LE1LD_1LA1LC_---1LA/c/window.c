/* window: exact runs of the F08 zone orbit over windows of 3*2^D sweeps, by periods of the cascade.
 *
 *   window STATE M [timeline] [check SWEEPS]
 *
 * The four machines with the `111110` block (1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA,
 * 1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA, 1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA,
 * 1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB) have the zone orbit of lean/Zone.lean, which lean/Cascade.lean
 * recasts as a cascade: the word Z is a row of one-bit cells, every sweep is one event (F, P0 or P1) that
 * enters cell 0 and travels outwards (swr_feed_ok).  A cell with bit x:
 *     F -> x := !x, nothing goes on;  P0 -> F if x = 0, else P1;  P1 -> P x, x := !x.
 * Cell 0 is fed P(pat n), pat n = (n mod 3 != 2), one event per sweep.
 *
 * Cells [0,m) only see what enters cell 0, so they are periodic (zone_period): W_0 = the three events of one
 * period of the block, W_{m+1} = cell m applied to W_m once if its bit is back afterwards, else twice (then
 * its bit is back: cell_bit).  D_m = number of cells in [0,m) that needed two passes; W_m is, in order, every
 * event that enters cell m during the first 3*2^D_m sweeps.  Pushing W_m once through cells m..|Z|-1 gives,
 * in order, every event that reaches each later cell in that window, and every event that leaves the word
 * (an F leaving is a halt, swr_feed_halt; a P leaving is a reset, swr_feed_reset).  No assumption is made
 * about the stranded block or the zones: the whole word is run.
 *
 * timeline: for every m <= M at which D grows, push W_m through the rest and print one line
 *           (D, |W_m|, events into the stranded block, into the old zone, leaving the word).
 * check S:  also run the orbit sweep by sweep for S sweeps (S <= window) and compare, at every cut >= M,
 *           the number of events reaching it; S = 3*2^D makes the comparison exact.
 * The timeline line also gives lossless_from: the first cut from which the count stays that of the old zone's
 * entrance (from there on nothing is absorbed until the old zone; for 1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA,
 * where nothing gets through, the first cut that no event reaches).
 * Env: CAP bytes per buffer (default 2e9, three buffers); PROFILE=file writes "cut count" for every cut;
 * DUMP=c prints the stream at cut c (F, 0 = P0, 1 = P1).
 * lean/Window.lean proves the method (wfold_run, window_quiet) and lean/WindowRun.lean evaluates it.
 * Build: gcc -O2 -o window window.c */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static unsigned char *Z, *Z0, *Zt;
static inline unsigned char cell(unsigned char *x, unsigned char e) {
  if (e == 0) { *x ^= 1; return 3; }
  if (e == 1) return *x ? 2 : 0;
  unsigned char o = *x ? 2 : 1; *x ^= 1; return o;
}
static long L, A, B, dumpcut = -1;
/* push S events of W through cells [m, L) of a copy of Z; cnt[j] = events reaching cell j (j = L: leaving) */
static void push(const unsigned char *W, long S, long m, unsigned char *buf1, unsigned char *buf2, long *cnt, int *first) {
  memcpy(Zt, Z, L); memcpy(buf1, W, S); unsigned char *a = buf1, *b = buf2;
  for (long j = 0; j <= L; j++) cnt[j] = 0;
  cnt[m] = S; *first = -1;
  for (long j = m; j < L && S > 0; j++) { unsigned char x = Zt[j]; long K = 0;
    for (long i = 0; i < S; i++) { unsigned char e = cell(&x, a[i]); if (e != 3) b[K++] = e; }
    unsigned char *t = a; a = b; b = t; S = K; cnt[j + 1] = S;
    if (dumpcut == j + 1) { printf("stream at cut %ld (%ld events): ", j + 1, S); for (long i = 0; i < S && i < 400; i++) putchar("F01"[a[i]]); putchar('\n'); } }
  if (cnt[L] > 0) *first = a[0];
}
int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: window STATE M [timeline] [check SWEEPS]\n"); return 2; }
  FILE *f = fopen(argv[1], "r"); unsigned long long t, n; long rl;
  if (!f || fscanf(f, "%llu %llu %ld ", &t, &n, &rl) != 3 || rl != 0) { fprintf(stderr, "bad state\n"); return 2; }
  Z = malloc(1 << 24); Z0 = malloc(1 << 24); Zt = malloc(1 << 24);
  int ch; L = 0; while ((ch = fgetc(f)) == '0' || ch == '1') Z[L++] = ch - '0';
  memcpy(Z0, Z, L);
  if (getenv("DUMP")) dumpcut = atol(getenv("DUMP"));
  long M = atol(argv[2]); int tl = 0; long long CHK = 0;
  for (int i = 3; i < argc; i++) { if (!strcmp(argv[i], "timeline")) tl = 1;
    else if (!strcmp(argv[i], "check") && i + 1 < argc) CHK = atoll(argv[++i]); }
  if (M > L) M = L;
  A = 0; B = 0;
  for (long i = 0; i < L;) { long j = i; while (j + 3 < L && Z[j + 3] == Z[j]) j++; if (j + 3 - i > B - A) { A = i; B = j + 3; } i = j + 1; }
  printf("state: zone step %llu, n = %llu; word %ld cells: new zone [0,%ld), stranded block [%ld,%ld), old zone [%ld,%ld)\n",
         t, n, L, A, A, B, B, L);
  long CAP = atol(getenv("CAP") ? getenv("CAP") : "2000000000");
  unsigned char *W = malloc(CAP), *W2 = malloc(CAP), *W3 = malloc(CAP);
  long *cnt = malloc((L + 1) * sizeof(long)); int first;
  long N = 3; int D = 0;
  for (int i = 0; i < 3; i++) W[i] = ((n + i) % 3 != 2) ? 2 : 1;
  if (tl) printf("timeline: D |W_m| m into_block into_old_zone leaving\n");
  for (long m = 0; m <= M; m++) {
    if (m == M) break;
    unsigned char x0 = Z[m], x = x0; long K = 0; int reps = 0;
    do { reps++; for (long i = 0; i < N; i++) { unsigned char e = cell(&x, W[i]);
        if (e != 3) { if (K >= CAP) { printf("CAP reached at cut %ld\n", m); return 1; } W2[K++] = e; } } } while (x != x0);
    unsigned char *tp = W; W = W2; W2 = tp; N = K;
    if (reps > 1) { D++;
      if (tl) { push(W, N, m + 1, W2, W3, cnt, &first);
        long pl = m + 1; while (pl < B && cnt[pl] != cnt[B]) pl++;
        printf("D %3d |W| %11ld m %4ld block %ld old %ld leave %ld lossless_from %ld%s\n", D, N, m + 1, m + 1 <= A ? cnt[A] : -1, cnt[B], cnt[L], pl,
               cnt[L] ? (first == 0 ? " HALT" : " RESET") : ""); fflush(stdout); } }
  }
  printf("cut %ld: |W| = %ld, window = 3*2^%d sweeps\n", M, N, D); fflush(stdout);
  push(W, N, M, W2, W3, cnt, &first);
  printf("events into the stranded block: %ld\n", M <= A ? cnt[A] : -1);
  printf("events into the old zone: %ld\n", cnt[B]);
  printf("events leaving the word: %ld%s\n", cnt[L], cnt[L] ? (first == 0 ? " (first: F, HALT)" : " (first: P, RESET)") : "");
  if (getenv("PROFILE")) { FILE *pf = fopen(getenv("PROFILE"), "w"); for (long j = M; j <= L; j++) fprintf(pf, "%ld %ld\n", j, cnt[j]); fclose(pf); }
  if (CHK > 0) {
    unsigned char *Zd = malloc(L); memcpy(Zd, Z0, L); long *dc = calloc(L + 1, sizeof(long)); unsigned long long nn = n;
    for (long long s = 0; s < CHK; s++) { unsigned char e = ((nn % 3) != 2) ? 2 : 1; long j = 0;
      for (; j < L && e != 3; j++) { dc[j]++; e = cell(&Zd[j], e); } if (e != 3) dc[L]++; nn++; }
    long bad = -1; for (long j = M; j <= L; j++) if (dc[j] != cnt[j]) { bad = j; break; }
    if (bad < 0) printf("check: %lld sweeps run one by one; counts agree at every cut from %ld on\n", CHK, M);
    else printf("check: MISMATCH at cut %ld: direct %ld, window %ld\n", bad, dc[bad], cnt[bad]);
  }
  return 0;
}
