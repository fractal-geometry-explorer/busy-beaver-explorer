/* framemap.c: iterate the Lean frame map `next` of lean/Phases.lean (as C in framemap_cases.h, generated from the
   Lean files by py/gen_c.py) from Ph.g 0 1, the frame the blank-tape run reaches at step 6.

     gcc -O2 -o framemap holdouts/1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE/c/framemap.c
     ./framemap run FRAMES [EVERY [STATE_FILE]]   iterate; print a checkpoint line every EVERY frames f; save the state
                                                 there too, and resume from it if it exists
     NOACCEL=1 ./framemap run ...                one case at a time (no sweep acceleration)
     ./framemap dump FRAMES                      print each frame "j kind x.. steps" (to compare with the Python map)

   Machine steps are counted exactly in 128 bits (6 for the start plus the step count of every case, from the piece
   theorems of lean/Pieces.lean).  The frame variables are uint64; the run stops if one reaches 2^60.  Besides the
   per-case counts, it watches the halting test of the bbchallenge rule form: a frame f(x, y) is the tape B(x, y), and
   B(x, 2x + 1) halts.  For every frame f it computes d = y - (2x + 1) and logs each new record of small |d| / x. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
typedef uint64_t u64;
typedef unsigned __int128 u128;
#include "framemap_cases.h"

static char *u128s(u128 v, char *buf) {
  char t[64]; int n = 0;
  if (!v) { strcpy(buf, "0"); return buf; }
  while (v) { t[n++] = '0' + (int)(v % 10); v /= 10; }
  for (int i = 0; i < n; i++) buf[i] = t[n - 1 - i];
  buf[n] = 0; return buf;
}
static u128 u128p(const char *s) { u128 v = 0; while (*s >= '0' && *s <= '9') v = v * 10 + (*s++ - '0'); return v; }

#define DH 16
#define RB 4
#define RBW 20
#define NRB (2 * RB * RBW)
typedef struct {
  u128 frames, steps, nf;
  int kind; u64 x[3];
  u128 cnt[NCASES];
  u64 maxv;
  double best;            /* smallest |d| / x seen at a frame f (d = y - (2x + 1)) */
  u64 dmin_abs;           /* smallest |d| seen at a frame f with x >= 1000 */
  u64 dh[2 * DH + 1];     /* frames f with x >= 16 by d, |d| <= DH */
  u64 nodd;               /* frames f with x >= 16 and y odd (only those can be B(x, 2x + 1)) */
  double hsum;            /* sum of 1/x over them */
  u64 rh[NRB];            /* them by d/x in bins of width 1/RBW over [-RB, RB) (outside: end bins) */
} St;

static int save(const char *fn, St *s) {
  char tmp[4096]; snprintf(tmp, sizeof tmp, "%s.tmp", fn);
  FILE *f = fopen(tmp, "w"); if (!f) return -1;
  char a[64], b[64], c[64];
  fprintf(f, "%s %s %s %d %llu %llu %llu %llu %.17g %llu\n", u128s(s->frames, a), u128s(s->steps, b), u128s(s->nf, c),
          s->kind, (unsigned long long)s->x[0], (unsigned long long)s->x[1], (unsigned long long)s->x[2],
          (unsigned long long)s->maxv, s->best, (unsigned long long)s->dmin_abs);
  for (int i = 0; i < NCASES; i++) fprintf(f, "%s\n", u128s(s->cnt[i], a));
  for (int i = 0; i <= 2 * DH; i++) fprintf(f, "%llu\n", (unsigned long long)s->dh[i]);
  fprintf(f, "%llu %.17g\n", (unsigned long long)s->nodd, s->hsum);
  for (int i = 0; i < NRB; i++) fprintf(f, "%llu\n", (unsigned long long)s->rh[i]);
  fclose(f); return rename(tmp, fn);
}
static int load(const char *fn, St *s) {
  FILE *f = fopen(fn, "r"); if (!f) return 0;
  char a[64], b[64], c[64]; unsigned long long x0, x1, x2, mv, dm;
  if (fscanf(f, "%63s %63s %63s %d %llu %llu %llu %llu %lg %llu", a, b, c, &s->kind, &x0, &x1, &x2, &mv, &s->best, &dm) != 10) { fclose(f); return 0; }
  s->frames = u128p(a); s->steps = u128p(b); s->nf = u128p(c); s->x[0] = x0; s->x[1] = x1; s->x[2] = x2; s->maxv = mv; s->dmin_abs = dm;
  for (int i = 0; i < NCASES; i++) { if (fscanf(f, "%63s", a) != 1) { fclose(f); return 0; } s->cnt[i] = u128p(a); }
  for (int i = 0; i <= 2 * DH; i++) { unsigned long long v; if (fscanf(f, "%llu", &v) != 1) { fclose(f); return 0; } s->dh[i] = v; }
  { unsigned long long v; if (fscanf(f, "%llu %lg", &v, &s->hsum) != 2) { fclose(f); return 0; } s->nodd = v; }
  for (int i = 0; i < NRB; i++) { unsigned long long v; if (fscanf(f, "%llu", &v) != 1) { fclose(f); return 0; } s->rh[i] = v; }
  fclose(f); return 1;
}

static void show(const char *tag, St *s) {
  char a[64], b[64], c[64];
  printf("%s frames %s steps %s (1e%.3f) f-frames %s frame %c", tag, u128s(s->frames, a), u128s(s->steps, b),
         log10((double)s->steps), u128s(s->nf, c), KNAME[s->kind]);
  for (int i = 0; i < ARITY[s->kind]; i++) printf(" %llu", (unsigned long long)s->x[i]);
  printf(" maxvar %llu best|d|/x %.3g min|d|(x>=1000) %llu\n", (unsigned long long)s->maxv, s->best, (unsigned long long)s->dmin_abs);
  fflush(stdout);
}

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: framemap run FRAMES [EVERY [STATE]] | dump FRAMES\n"); return 2; }
  setvbuf(stdout, NULL, _IOLBF, 0);
  int dump = !strcmp(argv[1], "dump");
  u128 N = u128p(argv[2]);
  u128 every = argc > 3 ? u128p(argv[3]) : (u128)1000000000;
  const char *sf = argc > 4 ? argv[4] : NULL;
  St s; memset(&s, 0, sizeof s);
  s.kind = (int)(strchr(KNAME, 'g') - KNAME); s.x[0] = 0; s.x[1] = 1; s.steps = 6; s.best = 1e300; s.dmin_abs = UINT64_MAX;
  if (sf && load(sf, &s)) show("resume", &s);
  const int KF = (int)(strchr(KNAME, 'f') - KNAME), KE = (int)(strchr(KNAME, 'e') - KNAME);
  int CE = -1, CH = -1;
  for (int i = 0; i < NCASES; i++) {
    if (!strcmp(CASE_NAME[i], "e l (j + 2) (r + 2)")) CE = i;
    if (!strcmp(CASE_NAME[i], "h l (m + 1) (r + 2)")) CH = i;
  }
  int accel = !dump && !getenv("NOACCEL") && CE >= 0 && CH >= 0;
  const u64 LIM = (u64)1 << 60;
  time_t t0 = time(NULL);
  u128 next_cp = (s.nf / every + 1) * every;
  while (s.frames < N) {
    /* the sweep below may pass N by up to its length; the final line reports the exact frame reached */
    if (dump) {
      char b[64]; printf("%llu %c", (unsigned long long)s.frames, KNAME[s.kind]);
      for (int i = 0; i < ARITY[s.kind]; i++) printf(" %llu", (unsigned long long)s.x[i]);
      printf(" %s\n", u128s(s.steps, b));
    }
    if (s.kind == KF) {
      u64 x = s.x[0], y = s.x[1];
      s.nf++;
      if (x >= 1) {
        u64 t = 2 * x + 1, ad = y > t ? y - t : t - y;
        double r = (double)ad / (double)x;
        if (x >= 1000 && ad < s.dmin_abs) s.dmin_abs = ad;
        if (x >= 16 && ad <= DH) s.dh[DH + (y > t ? (int)ad : -(int)ad)]++;
        if (x >= 16 && (y & 1)) {
          s.nodd++; s.hsum += 1.0 / (double)x;
          double bb = floor(((double)y - (double)t) / (double)x * RBW) + RB * RBW;   /* clamp before the cast */
          int b = bb < 0 ? 0 : bb >= NRB ? NRB - 1 : (int)bb;
          s.rh[b]++;
        }
        if (r < s.best) {
          char a[64], b[64];
          s.best = r;
          if (!dump) printf("near frame %s step %s f %llu %llu d %lld |d|/x %.4g\n", u128s(s.frames, a), u128s(s.steps, b),
                            (unsigned long long)x, (unsigned long long)y, (long long)y - (long long)t, r);
        }
      }
    }
    if (accel && s.kind == KE && s.x[1] >= 2 && s.x[2] >= 3) {
      /* sweep: e L J R -> h (L+2) (J-1) (R-1) -> e (L+2) (J-1) (R-2), cases "e l (j + 2) (r + 2)" (2J + 7 steps) and
         "h l (m + 1) (r + 2)" (2J - 1 steps); valid while J >= 2 and R >= 3 (lemma `sweep` in lean/Sweep.lean) */
      u64 J = s.x[1], R = s.x[2], k = J - 1, k2 = (R - 3) / 2 + 1;
      if (k2 < k) k = k2;
      s.x[0] += 2 * k; s.x[1] -= k; s.x[2] -= 2 * k;
      s.steps += (u128)k * (4 * (u128)J + 6) - 2 * (u128)k * (k - 1);
      s.frames += 2 * (u128)k; s.cnt[CE] += k; s.cnt[CH] += k;
      if (s.x[0] > s.maxv) { s.maxv = s.x[0]; if (s.maxv >= LIM) { show("overflow", &s); return 1; } }
      goto checkpoint;
    }
    u64 dt; int halt;
    int c = lean_next(&s.kind, s.x, &dt, &halt);
    if (c < 0) { printf("NO CASE\n"); show("stuck", &s); return 1; }
    s.cnt[c]++;
    s.steps += dt;
    s.frames++;
    if (halt) { char b[64]; printf("HALT case %s at step %s\n", CASE_NAME[c], u128s(s.steps, b)); show("halt", &s); return 0; }
    for (int i = 0; i < ARITY[s.kind]; i++) if (s.x[i] > s.maxv) { s.maxv = s.x[i]; if (s.maxv >= LIM) { show("overflow", &s); return 1; } }
  checkpoint:
    if (s.steps >> 126) { show("step counter near 2^128", &s); if (sf) save(sf, &s); return 1; }
    if (!dump && s.nf >= next_cp) {
      next_cp += every;
      char tag[64]; snprintf(tag, sizeof tag, "cp %lds", (long)(time(NULL) - t0));
      show(tag, &s);
      if (sf) save(sf, &s);
    }
  }
  if (!dump) {
    show("end", &s);
    for (int i = 0; i < NCASES; i++) if (s.cnt[i]) { char a[64]; printf("case %-28s %s\n", CASE_NAME[i], u128s(s.cnt[i], a)); }
    {
      /* only frames with y odd (d even) can be B(x, 2x + 1); a guide to how many d = 0 a "random" orbit would have
         had: the mean count at the 16 even d with 0 < |d| <= 16 */
      u64 tot = 0;
      for (int dd = -DH; dd <= DH; dd += 2) if (dd) tot += s.dh[DH + dd];
      printf("odd-y frames f (x >= 16): %llu, sum 1/x %.6g; at even d, 0 < |d| <= %d: %llu, mean per value %.3g; at d = 0: %llu\n",
             (unsigned long long)s.nodd, s.hsum, DH, (unsigned long long)tot, tot / (double)DH, (unsigned long long)s.dh[DH]);
      printf("their d/x histogram (bins of 1/%d from -%d; end bins hold the rest):", RBW, RB);
      for (int i = 0; i < NRB; i++) printf(" %llu", (unsigned long long)s.rh[i]);
      printf("\n");
    }
    printf("frames f with x >= 16 by d = y - (2x + 1):");
    for (int i = 0; i <= 2 * DH; i++) printf(" %d:%llu", i - DH, (unsigned long long)s.dh[i]);
    printf("\n");
    if (sf) save(sf, &s);
  }
  return 0;
}
