// nearmiss.c: how close does the word run of 1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB--- come to the dangerous word end?
// The real run is wordrun.c (mode 0RD).  In every round r, when the pass first reaches a block start P at least
// DEPTH cells before the old word end, the count n there is replaced by a perturbed value n' (n-2, n-1, n+1, n+2, 2n,
// n/2), and the rest of that round and the next H rounds are recomputed on a copy of the word end.  The later rounds
// use the real run's own count at its last block start s <= P, and P becomes s (the cells left of P are the same in
// both runs, so that count is exact).  A perturbed run is "dangerous" if it meets 1111 (halt) or 11100 (no rule).
// usage: ./nearmiss 0RD|0LF ROUNDS [DEPTH [H]]   (0LF: 1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA---, every 111 halts;
//   the real runs of the two machines are the same as long as no 111 is met, which wordrun.c checks)
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef unsigned __int128 u128;
static uint8_t *T; static long F, E;
static const long N = 1L << 28;
#define BUF 1024
#define NP 6
#define MAXX 64
typedef struct { int live; long base, P; int left; uint8_t t[BUF]; int kind; long r0; long n0, n1; int junk; long cand_s; u128 cand_c; int cand_ok; } Exp;
static Exp X[MAXX];
static int lf;  // 1: 1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA---, which halts on every 111
// one pass of n visits from absolute position s on an experiment tape; returns 0 ok, 1 halt, 2 stuck, 3 overflow
static int pass(Exp *x, long s, u128 n) {
  long p = s - x->base;
  while (n > 0) {
    if (p < 0 || p + 8 >= BUF) return 3;
    uint8_t *w = x->t + p;
    if (w[0] == 0) { w[0] = 1; n--; if (n == 0 && w[1] == 1) x->junk++; }
    else if (w[2] == 0) { u128 m = n - 1; w[0] = m & 1; w[1] = 0; n = 1 + m / 2; p += 3; }
    else if (w[1] == 0 && w[3] == 0) { n *= 2; p += 4; if (n >> 120) return 3; }
    else if (w[1] == 0) { w[0] = 0; w[2] = 0; w[3] = 1; n--; if (n == 0 && w[4] == 1) x->junk++; }
    else { if (lf || w[3] == 1) return 1; if (w[4] == 1) { w[1] = 0; n--; } else return 2; }
  }
  return 0;
}
int main(int argc, char **argv) {
  setvbuf(stdout, NULL, _IOLBF, 0);
  if (argc < 3) { fprintf(stderr, "usage: %s 0RD|0LF ROUNDS [DEPTH [H]]\n", argv[0]); return 2; }
  lf = !strcmp(argv[1], "0LF"); long R = atol(argv[2]); long DEPTH = argc > 3 ? atol(argv[3]) : 60; int H = argc > 4 ? atoi(argv[4]) : 6;
  T = calloc(N, 1); F = N / 4; E = F + 1; T[F] = 1;
  long ndanger[NP] = {0}, nexp[NP] = {0};
  for (long r = 1; r <= R; r++) {
    F -= 2; T[F] = 1; T[F + 1] = 0;
    long p = F, e = 0; int big = 0; u128 c = 1; long oldE = E;
    int took = 0; long P = 0; u128 nP = 0; uint8_t snap[BUF]; long sbase = 0;
    while (big || c > 0) {
      uint8_t *w = T + p;
      int start = !(w[0] == 0);  // a block start (rule other than the single 0)
      if (start && oldE - p < 400) {
        for (int i = 0; i < MAXX; i++) if (X[i].live && p <= X[i].P) {
          if (big && e > 118) X[i].cand_ok = 0;
          else { X[i].cand_ok = 1; X[i].cand_s = p; X[i].cand_c = big ? (((u128)1) << e) - c : c; }
        }
      }
      if (start && !took && p >= oldE - DEPTH && r > 20) {
        took = 1;
        if (!big) { P = p; nP = c; sbase = P - 16; memcpy(snap, T + sbase, BUF); } else P = -1;
      }
      if (w[0] == 0) { w[0] = 1; if (big) c++; else c--; }
      else if (w[2] == 0) {
        if (big) { u128 c1 = c + 1; w[0] = c1 & 1; e -= 1; c = (c1 + 1) / 2 - 1; }
        else { u128 n1 = c - 1; w[0] = n1 & 1; c = 1 + n1 / 2; }
        w[1] = 0; p += 3;
      } else if (w[1] == 0 && w[3] == 0) { if (big) e++; c *= 2; p += 4; }
      else if (w[1] == 0) { w[0] = 0; w[2] = 0; w[3] = 1; if (big) c++; else c--; }
      else { if (lf || w[3] == 1) { printf("REAL HALT %ld\n", r); return 0; } if (w[4] == 1) { w[1] = 0; if (big) c++; else c--; } else { printf("REAL STUCK %ld\n", r); return 0; } }
      if (big) { if (e <= 100) { c = (((u128)1) << e) - c; big = 0; } }
      else if (c >> 110) { int k = 0; while (((u128)1 << k) < c) k++; c = (((u128)1) << k) - c; e = k; big = 1; }
    }
    if (p + 4 > E) E = p + 4;
    while (E > F && T[E - 1] == 0) E--;
    // advance pending experiments by this round
    for (int i = 0; i < MAXX; i++) if (X[i].live) {
      Exp *x = X + i;
      if (!x->cand_ok) { x->live = 0; continue; }
      if (x->cand_s - x->base < 8) { x->live = 0; continue; }
      memcpy(x->t, T + x->base, x->cand_s - x->base);  // cells left of s: the same in both runs
      int res = pass(x, x->cand_s, x->cand_c); x->cand_ok = 0; x->P = x->cand_s;
      if (res == 1 || res == 2) {
        ndanger[x->kind]++; x->live = 0;
        printf("DANGER round %ld kind %d perturbed in round %ld (n=%ld -> %ld) %s after %d rounds\n", r, x->kind, x->r0, x->n0, x->n1, res == 1 ? "HALT" : "STUCK", H - x->left + 1);
      } else if (res == 3 || --x->left == 0) x->live = 0;
    }
    // start new experiments from this round
    if (took && P > 0) {
      for (int k = 0; k < NP; k++) {
        u128 n2 = k == 0 ? nP - 2 : k == 1 ? nP - 1 : k == 2 ? nP + 1 : k == 3 ? nP + 2 : k == 4 ? 2 * nP : nP / 2;
        if (n2 == 0 || nP < 3) continue;
        int slot = -1; for (int i = 0; i < MAXX; i++) if (!X[i].live) { slot = i; break; }
        if (slot < 0) { fprintf(stderr, "no slot\n"); return 1; }
        Exp *x = X + slot; x->live = 1; x->base = sbase; x->P = P; x->left = H; memcpy(x->t, snap, BUF);
        x->kind = k; x->r0 = r; x->n0 = (long)nP; x->n1 = (long)n2; x->junk = 0; x->cand_ok = 0; nexp[k]++;
        int res = pass(x, P, n2);
        if (res == 1 || res == 2) { ndanger[k]++; x->live = 0; printf("DANGER round %ld kind %d perturbed in round %ld (n=%ld -> %ld) %s in the same round\n", r, k, r, (long)nP, (long)n2, res == 1 ? "HALT" : "STUCK"); }
        else if (res == 3) x->live = 0;
      }
    }
    if (r % 20000 == 0) { fprintf(stderr, "round %ld:", r); for (int k = 0; k < NP; k++) fprintf(stderr, " %ld/%ld", ndanger[k], nexp[k]); fprintf(stderr, "\n"); }
  }
  printf("DONE %ld rounds depth %ld H %d; dangerous/started per perturbation (n-2 n-1 n+1 n+2 2n n/2):", R, DEPTH, H);
  for (int k = 0; k < NP; k++) printf(" %ld/%ld", ndanger[k], nexp[k]);
  printf("\n");
  return 0;
}
