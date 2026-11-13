// Check the counter model of 1RB1RF_1LC0LB_1RE1LD_1RE0LB_1RA0RE_---0RC against direct simulation.
// A visit is a moment when the head is in state C on the blank cell right of the tape.  At a steady visit the tape is
//   0^inf [1] U(b_top)..U(b_1) b_0 0 1  M(t)  I(i)  (1011)^m 1 0  C>0      (U(b) = b01101, the lone 1 only in phase B)
// The program parses every visit into (phase, V, width, t, i, m) and checks each consecutive pair against the rule
//   i<7: i -> i+1;  i=7: i -> 0, t -> 1-t, V -> V + (t ? 42 : 39);  m -> m+1 always;
// with V's overflow: phase A -> phase B (V mod 2^w, same width), phase B -> phase A (one more digit, after a transient).
// Every visit that does not parse, or a pair that breaks the rule, is printed as an exception.
// usage: gcc -O2 -o visits visits.c && ./visits STEPS
#include "../../../tools/c/tm.h"
static const char *MA[2] = {"110110111010011101110111011011101110111011101", "110110111011011101110111011011101110111011101"};
typedef struct { int ok; char ph; int w; long long V; int t, i; long long m; } vis;
static int match(tm_tape *t, long long p, const char *s) { for (int j = 0; s[j]; j++) if (tm_get(t, p + j) != s[j] - '0') return 0; return 1; }
static vis parse(tm_tape *t) {
  vis v = {0};
  long long e = t->hi - 1; // cells e-1, e are "1 0"; the head is at hi on the blank
  if (!(tm_get(t, e - 1) == 1 && tm_get(t, e) == 0)) return v;
  e -= 1; while (match(t, e - 4, "1011")) { e -= 4; v.m++; }
  // I(i) = i2 01101 i1 01101 i0 01 : 15 cells ending at e-1
  long long q = e - 15;
  if (!match(t, q + 1, "01101") || !match(t, q + 7, "01101") || !match(t, q + 13, "01")) return v;
  v.i = 4 * tm_get(t, q) + 2 * tm_get(t, q + 6) + tm_get(t, q + 12);
  q -= 45; if (match(t, q, MA[0])) v.t = 0; else if (match(t, q, MA[1])) v.t = 1; else return v;
  // digits: from the left end, phase A: U(b) words then b0 0 1; phase B: a lone 1 first
  long long p = t->lo; while (tm_get(t, p) == 0) p++;
  long long r = q - 3; // b0 0 1 at r
  if (!match(t, r + 1, "01")) return v;
  int phA = ((r - p) % 6 == 0), phB = ((r - p) % 6 == 1 && tm_get(t, p) == 1);
  if (!phA && !phB) return v;
  long long s = phB ? p + 1 : p; v.ph = phB ? 'B' : 'A'; v.V = 0; v.w = 0;
  for (; s < r; s += 6) { if (!match(t, s + 1, "01101")) return v; v.V = 2 * v.V + tm_get(t, s); v.w++; }
  v.V = 2 * v.V + tm_get(t, r); v.w++;
  if (v.ph == 'A' && (v.V >> (v.w - 1)) != 1) return v;
  v.ok = 1; return v;
}
int main(int argc, char **argv) {
  tm_machine M; tm_parse("1RB1RF_1LC0LB_1RE1LD_1RE0LB_1RA0RE_---0RC", &M);
  long long max = atoll(argv[1]); tm_tape t; tm_tape_init(&t, 1 << 22); int st = 0;
  long long k = 0, visits = 0, steady = 0, shallow = 0, deep = 0, exc = 0, ovA = 0, ovB = 0; vis pv = {0};
  while (k < max) {
    if (t.head == t.hi && st == 2 && tm_get(&t, t.head) == 0) {
      visits++; vis v = parse(&t);
      if (v.ok) steady++;
      if (pv.ok && v.ok) {
        int good = v.m == pv.m + 1;
        if (pv.i < 7) { good &= v.ph == pv.ph && v.w == pv.w && v.V == pv.V && v.t == pv.t && v.i == pv.i + 1; if (good) shallow++; }
        else {
          long long nv = pv.V + (pv.t ? 42 : 39); good &= v.t == 1 - pv.t && v.i == 0;
          if (nv < (1LL << pv.w)) { good &= v.ph == pv.ph && v.w == pv.w && v.V == nv; if (good) deep++; }
          else if (pv.ph == 'A') { good &= v.ph == 'B' && v.w == pv.w && v.V == nv - (1LL << pv.w); if (good) { ovA++; printf("A-overflow at visit %lld step %lld: B w=%d V=%lld\n", visits, k, v.w, v.V); } }
          else good = 0; // phase B overflow: a transient, never a steady visit next
        }
        if (!good) { exc++; printf("exception at visit %lld step %lld: %c w=%d V=%lld t=%d i=%d -> %c w=%d V=%lld t=%d i=%d\n", visits, k, pv.ph, pv.w, pv.V, pv.t, pv.i, v.ph, v.w, v.V, v.t, v.i); }
      } else if (pv.ok != v.ok) {
        printf("%s at visit %lld step %lld", v.ok ? "steady again" : "transient", visits, k);
        if (v.ok) { printf(": %c w=%d V=%lld t=%d i=%d m=%lld", v.ph, v.w, v.V, v.t, v.i, v.m); if (v.ph == 'A') ovB++; }
        printf("\n");
      }
      pv = v;
    }
    if (!tm_step(&M, &t, &st)) { printf("HALT at step %lld\n", k + 1); return 0; }
    k++;
  }
  printf("%lld steps, %lld visits, %lld steady; rule holds for %lld shallow, %lld deep, %lld A-overflow pairs; %lld exceptions; %lld steady phase-A epochs started (the first at visit 280, after the start-up)\n",
         k, visits, steady, shallow, deep, ovA, exc, ovB);
}
