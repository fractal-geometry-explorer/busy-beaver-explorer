// patcount: the counter program of a Turing machine made from n-gram counts, explored on the capped
// domain "exact if at most K, else big". See README.md.
//
// Abstract configuration: state q, head position mod m, an exact window of 2n-1 cells centred on the head, and
// for each side a vector of counts. The right vector counts, for each n-gram p and phase f, the n-grams equal
// to p that start at a position s >= head+1 with s mod m = f and s <= (last non-zero cell of the tape).
// The left vector is the mirror image (n-grams ending at <= head-1 and at or after the first non-zero cell).
// A step to the right appends the n-gram at offsets -(n-1)..0 to the left vector and removes from the right
// vector the n-gram at offsets 1..n; its last cell is the newly revealed window cell. Which of the two
// candidates is removed is not known: both are tried, subject to
//   (a) its count is positive,
//   (b) what remains can still be the n-gram counts of a half tape: degree balance at each (n-1)-gram and
//       reachability of every remaining n-gram from the new border (Euler trail conditions).
// Counts above K are remembered only as "big"; big-1 is big or K.
//
// usage: patcount TM n m K [maxstates] [certfile]
// output: SAFE states=..  |  HALT ..  |  LIMIT ..
#include <bits/stdc++.h>
using namespace std;
typedef basic_string<uint8_t> Vec; // d counters, 255 = big
const uint8_t BIG = 255;
int n, m, K, NS, NG, NN, WB, R, dside, d; // NG=2^n grams, NN=2^(n-1) nodes
struct Tr { int w, dir, ns; bool def; } tr[8][2];
static inline int md(int a) { return ((a % m) + m) % m; }
// counter index of gram p with start phase f on side s (0 left, 1 right)
static inline int cidx(int s, int f, int p) { return s * dside + f * NG + p; }
static inline bool pos(uint8_t x) { return x != 0; }
// Is the side vector (side s) with border node (y, f) realisable?  y = the n-1 known cells next to the head,
// f = phase of the first (leftmost) cell of y.
// Edges: gram p at start phase f joins node (p>>1, f) [its first n-1 cells] and node (p&(NN-1), f+1) [last n-1].
// Right side: trail runs from prefix node to suffix node. Left side: from suffix node to prefix node.
static bool feasible(const Vec& v, int s, int y, int f) {
  const uint8_t* c = v.data() + s * dside;
  bool any = false; for (int i = 0; i < dside; i++) if (c[i]) { any = true; break; }
  if (!any) return y == 0; // nothing counted: every remaining cell is zero
  // the last non-zero cell lies beyond or in the border: fine. Balance per node.
  int lo, hi; // range of (out - in) at each node, hi may be infinite
  static vector<char> seen; static vector<int> stack; seen.assign(NN * m, 0); stack.clear();
  for (int yy = 0; yy < NN; yy++) for (int ff = 0; ff < m; ff++) {
    // edges incident: as "trail-out" and "trail-in"
    int olo = 0, ohi = 0, ilo = 0, ihi = 0; bool oinf = false, iinf = false;
    for (int b = 0; b < 2; b++) {
      int pout, fout, pin, fin;
      if (s == 1) { pout = (yy << 1) | b; fout = ff; pin = (b << (n - 1)) | yy; fin = md(ff - 1); }
      else { pout = (b << (n - 1)) | yy; fout = md(ff - 1); pin = (yy << 1) | b; fin = ff; }
      uint8_t a = c[fout * NG + pout]; if (a == BIG) { olo += K + 1; oinf = true; } else { olo += a; ohi += a; }
      uint8_t e = c[fin * NG + pin]; if (e == BIG) { ilo += K + 1; iinf = true; } else { ilo += e; ihi += e; }
    }
    // need out - in = [node is border] - [node is terminal]; the terminal node is unknown (the node after the
    // last counted gram), so allow -1 at exactly ... we only check: out - in in {0, +1 (border), -1 (terminal)}.
    bool isb = (yy == y && ff == f);
    // feasible values of out-in: [olo - (iinf?inf:ihi), (oinf?inf:ohi) - ilo]
    int want_lo = isb ? 0 : -1, want_hi = isb ? 1 : 0;
    bool ok = true;
    if (!iinf && olo - ihi > want_hi) ok = false;
    if (!oinf && ohi - ilo < want_lo) ok = false;
    if (!ok) return false;
    (void)lo; (void)hi;
  }
  // connectivity: every positive gram reachable from the border along positive grams
  seen[y * m + f] = 1; stack.push_back(y * m + f);
  while (!stack.empty()) {
    int id = stack.back(); stack.pop_back(); int yy = id / m, ff = id % m;
    for (int b = 0; b < 2; b++) {
      int p, pf, ty, tf;
      if (s == 1) { p = (yy << 1) | b; pf = ff; ty = p & (NN - 1); tf = md(ff + 1); }
      else { p = (b << (n - 1)) | yy; pf = md(ff - 1); ty = p >> 1; tf = pf; }
      if (!c[pf * NG + p]) continue;
      int t = ty * m + tf; if (!seen[t]) { seen[t] = 1; stack.push_back(t); }
    }
  }
  for (int ff = 0; ff < m; ff++) for (int p = 0; p < NG; p++) if (c[ff * NG + p]) {
    int sy, sf; if (s == 1) { sy = p >> 1; sf = ff; } else { sy = p & (NN - 1); sf = md(ff + 1); }
    if (!seen[sy * m + sf]) return false;
  }
  return true;
}
struct St { long long ctl; Vec v; mutable const St* par; bool operator==(const St& o) const { return ctl == o.ctl && v == o.v; } };
struct H { size_t operator()(const St& s) const { return hash<string>()(string((const char*)s.v.data(), s.v.size())) * 1000003u + s.ctl; } };
int main(int argc, char** argv) {
  if (argc < 5) { fprintf(stderr, "usage: patcount TM n m K [maxstates] [certfile]\n"); return 2; }
  string tm = argv[1]; n = atoi(argv[2]); m = atoi(argv[3]); K = atoi(argv[4]);
  size_t maxst = argc > 5 ? atoll(argv[5]) : 20000000; const char* cert = argc > 6 ? argv[6] : 0;
  NS = (tm.size() + 1) / 7;
  for (int s = 0; s < NS; s++) for (int b = 0; b < 2; b++) {
    const char* t = tm.c_str() + s * 7 + b * 3;
    if (t[0] == '-') tr[s][b].def = false; else tr[s][b] = {t[0] - '0', t[1] == 'R' ? 1 : -1, t[2] - 'A', true};
  }
  R = getenv("RAD") ? atoi(getenv("RAD")) : n - 1; if (R < n - 1) R = n - 1;
  NG = 1 << n; NN = NG >> 1; WB = 2 * R + 1; dside = m * NG; d = 2 * dside;
  long long NW = 1LL << WB; // window cell at offset o stored at bit (R-o)
  auto ctl = [&](int q, int ph, long long w) { return ((long long)q * m + ph) * NW + w; };
  unordered_set<St, H> seen; deque<const St*> work;
  const St* cur = 0;
  auto add = [&](long long c, const Vec& v) { auto r = seen.insert({c, v, cur}); if (r.second) work.push_back(&*r.first); };
  if (getenv("START")) { // start from the abstraction of the real configuration after START steps
    long T = atol(getenv("START")); int Lm = 1 << 22; vector<char> tape(2 * Lm, 0); int h = Lm, q = 0, mn = 2 * Lm, mx = -1;
    for (long t = 0; t < T; t++) { const Tr& x = tr[q][(int)tape[h]]; if (!x.def) { printf("REALHALT %ld\n", t); return 0; } tape[h] = x.w; mn = min(mn, h); mx = max(mx, h); h += x.dir; q = x.ns; }
    while (mn <= mx && !tape[mn]) mn++; while (mx >= mn && !tape[mx]) mx--;
    Vec v(d, 0); auto cap = [&](uint8_t& x) { if (x != BIG) { if (x >= K) x = BIG; else x++; } };
    for (int s0 = h + R + 2 - n; s0 <= mx; s0++) { int p = 0; for (int j = 0; j < n; j++) p = p * 2 + tape[s0 + j]; cap(v[cidx(1, md(s0 - Lm), p)]); }
    for (int e0 = mn; e0 <= h - R - 2 + n; e0++) { int p = 0; for (int j = 0; j < n; j++) p = p * 2 + tape[e0 - n + 1 + j]; cap(v[cidx(0, md(e0 - n + 1 - Lm), p)]); }
    long long w = 0; for (int o = -R; o <= R; o++) w = w * 2 + tape[h + o];
    add(ctl(q, md(h - Lm), w), v);
  } else
  add(ctl(0, 0, 0), Vec(d, 0));
  bool halt = false; bool nodrop = getenv("NODROP") != 0; // NODROP: big-1 stays big; not sound for SAFE, used to find halting paths valid without a cap
  auto inc = [&](uint8_t& x) { if (x != BIG) { if (x >= K) x = BIG; else x++; } };
  while (!work.empty()) {
    const St* sp = work.front(); work.pop_front();
    if (seen.size() > maxst) { printf("LIMIT states=%zu\n", seen.size()); return 0; }
    cur = sp; long long c = sp->ctl; const Vec& v = sp->v;
    long long w = c % NW; int ph = (c / NW) % m, q = c / NW / m;
    int sym = (w >> R) & 1;
    const Tr& t = tr[q][sym];
    if (!t.def) { halt = true;
      if (getenv("TRACE")) { vector<const St*> path; for (const St* p = sp; p; p = p->par) path.push_back(p); reverse(path.begin(), path.end());
        for (auto p : path) { long long w = p->ctl % NW; int q = p->ctl / NW / m; printf("%c ", 'A' + q); for (int i = WB - 1; i >= 0; i--) { if (i == R) printf("["); printf("%d", (int)((w >> i) & 1)); if (i == R) printf("]"); }
          for (int s = 0; s < 2; s++) { printf(s ? "  R:" : "  L:"); for (int i = 0; i < dside; i++) if (p->v[s * dside + i]) { printf(" "); for (int j = n - 1; j >= 0; j--) printf("%d", ((i % NG) >> j) & 1); if (p->v[s * dside + i] == BIG) printf("=w"); else printf("=%d", p->v[s * dside + i]); } }
          printf("\n"); } }
      break; }
    long long w2 = (w & ~(1LL << R)) | ((long long)t.w << R);
    int S = t.dir == 1 ? 1 : 0;      // side that loses a gram
    int g, gf, x, pf;
    if (S == 1) { g = w2 >> (WB - n); gf = md(ph - R); x = w2 & (NN - 1); pf = md(ph + R + 2 - n); }
    else { g = w2 & (NG - 1); gf = md(ph + R - (n - 1)); x = w2 >> (WB - (n - 1)); pf = md(ph - R - 1); }
    Vec u = v;
    { // push g on side 1-S: counted iff it is non-zero or something is already counted there
      int o = (1 - S) * dside; bool any = g != 0;
      if (!any) for (int i = 0; i < dside; i++) if (u[o + i]) { any = true; break; }
      if (any) inc(u[cidx(1 - S, gf, g)]);
    }
    int nph = md(ph + t.dir);
    for (int b = 0; b < 2; b++) {
      int p = S == 1 ? ((x << 1) | b) : ((b << (n - 1)) | x);
      long long w3 = S == 1 ? (((w2 << 1) | b) & (NW - 1)) : ((w2 >> 1) | ((long long)b << (WB - 1)));
      // new border node on side S
      int by, bf;
      if (S == 1) { by = w3 & (NN - 1); bf = md(nph + R + 2 - n); } else { by = w3 >> (WB - (n - 1)); bf = md(nph - R); }
      uint8_t y = u[cidx(S, pf, p)];
      bool any = false; for (int i = 0; i < dside; i++) if (u[S * dside + i]) { any = true; break; }
      if (!any) { if (p == 0) add(ctl(t.ns, nph, w3), u); continue; } // beyond the last non-zero cell
      if (y == 0) continue;
      for (int alt = 0; alt < 2; alt++) {
        Vec u2 = u; uint8_t& z = u2[cidx(S, pf, p)];
        if (y == BIG) { if (alt == 1) { if (nodrop) break; z = K; } } else { if (alt == 1) break; z = y - 1; }
        if (!feasible(u2, S, by, bf)) continue;
        add(ctl(t.ns, nph, w3), u2);
      }
    }
  }
  if (halt) { int len = 0; bool big = false; for (const St* p = cur; p; p = p->par) { len++; for (auto x : p->v) if (x == BIG) big = true; }
    // the path is a path of the uncapped program if no "big-1 = K" step was used and no big counter is decremented more than K times
    // (sufficient: NODROP and fewer steps than K, since a big counter is above K and loses at most one per step)
    bool valid = !big || (nodrop && len <= K);
    printf("HALT states=%zu pathlen=%d path_exact=%s uncapped_valid=%s\n", seen.size(), len, big ? "no" : "yes", valid ? "yes" : "unknown"); return 0; }
  printf("SAFE states=%zu\n", seen.size());
  if (getenv("CHECK")) { // soundness self-test: the abstraction of every configuration of the real run must be in the set
    long T = atol(getenv("CHECK")); int Lm = 1 << 16; vector<int> tape(2 * Lm, 0); int h = Lm, q = 0, lo = h, hi = h; bool anynz = false; long bad = 0, t;
    int mn = Lm, mx = Lm; // first / last non-zero cell
    for (t = 0; t < T; t++) {
      Vec v(d, 0); auto cap = [&](uint8_t& x) { if (x != BIG) { if (x >= K) x = BIG; else x++; } };
      if (anynz) {
        for (int s0 = h + R + 2 - n; s0 <= mx; s0++) { int p = 0; for (int j = 0; j < n; j++) p = p * 2 + tape[s0 + j]; cap(v[cidx(1, md(s0 - Lm), p)]); }
        for (int e0 = mn; e0 <= h - R - 2 + n; e0++) { int p = 0; for (int j = 0; j < n; j++) p = p * 2 + tape[e0 - n + 1 + j]; cap(v[cidx(0, md(e0 - n + 1 - Lm), p)]); }
      }
      long long w = 0; for (int o = -R; o <= R; o++) w = w * 2 + tape[h + o];
      if (!seen.count({ctl(q, md(h - Lm), w), v, 0})) { bad++; if (bad == 1) printf("CHECK first miss at step %ld\n", t); }
      const Tr& x = tr[q][tape[h]]; if (!x.def) break;
      tape[h] = x.w; if (x.w) { anynz = true; mn = min(mn, h); mx = max(mx, h); }
      while (anynz && mn <= mx && !tape[mn]) mn++; while (anynz && mx >= mn && !tape[mx]) mx--; if (mn > mx) { anynz = false; mn = Lm; mx = Lm; }
      h += x.dir; q = x.ns; if (h < R + n + 2 || h > 2 * Lm - R - n - 2) break; (void)lo; (void)hi;
    }
    printf("CHECK steps=%ld misses=%ld\n", t, bad);
  }
  if (cert) {
    FILE* f = fopen(cert, "w"); fprintf(f, "%s %d %d %d %d\n", tm.c_str(), n, m, K, R);
    for (auto& s : seen) { fprintf(f, "%lld ", s.ctl); for (int i = 0; i < d; i++) fputc(s.v[i] == BIG ? 'w' : (s.v[i] < 10 ? '0' + s.v[i] : 'a' + s.v[i] - 10), f); fputc('\n', f); }
    fclose(f);
  }
  return 0;
}
