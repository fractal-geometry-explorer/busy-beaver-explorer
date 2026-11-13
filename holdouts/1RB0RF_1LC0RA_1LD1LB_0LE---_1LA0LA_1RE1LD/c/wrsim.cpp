// Word-run simulator: the tape is two stacks of runs w^n (w a short word), the head sits between two runs.
// Crossing a run w^n: if one copy of w, entered at its near edge in state q, is left at the far edge in state q,
// the whole run is crossed at once (n times the steps).  Otherwise one copy is run, or the run is rotated so that
// a rotation of w crosses.  Exact: same step count and tape as the plain machine at every macro step.
//
// usage: wrsim MACHINE TOKENS MAXSTEPS MAXSECONDS MAXLINES [MODE]
//   TOKENS: comma separated words kept as runs (e.g. 01 or 110,100)
//   prints "step side state tape" each time the head reaches the edge of the tape opposite to the last one (MODE 0)
//   or at every edge (MODE 1).
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <vector>
#include <string>
#include <unordered_map>
#include <ctime>
using namespace std;
typedef unsigned __int128 u128;
struct Run { uint32_t bits; uint8_t len; uint64_t cnt; };
struct Tr { int w, m, q; bool halt; } T[8][2];
int NS;
vector<pair<uint32_t,int>> TOK; // token words (bits left-to-right, len)
int MAXTL = 1;
static inline int cell(const Run& r, int i) { return (r.bits >> i) & 1; }
static string wstr(uint32_t b, int l) { string s; for (int i = 0; i < l; i++) s += char('0' + ((b >> i) & 1)); return s; }
static bool is_token(uint32_t b, int l) { for (auto& t : TOK) if (t.first == b && t.second == l) return true; return false; }

struct Res { uint32_t bits; int q; bool far; bool halt; uint64_t steps; };
unordered_map<uint64_t, Res> cache;
Res sim(int q, uint32_t bits, int len, int d) {
  uint64_t key = ((uint64_t)bits << 16) | ((uint64_t)len << 8) | ((uint64_t)q << 1) | (d == 1);
  auto it = cache.find(key); if (it != cache.end()) return it->second;
  int c[32]; for (int i = 0; i < len; i++) c[i] = (bits >> i) & 1;
  int i = d == 1 ? 0 : len - 1; uint64_t n = 0; Res r{};
  while (true) {
    Tr t = T[q][c[i]];
    if (t.halt) { r.halt = true; r.steps = n + 1; r.q = q; break; }
    c[i] = t.w; i += t.m; q = t.q; n++;
    if (i < 0 || i >= len) { r.far = d == 1 ? i >= len : i < 0; r.q = q; r.steps = n; break; }
    if (n > 100000) { fprintf(stderr, "loop in word\n"); exit(2); }
  }
  uint32_t b = 0; for (int k = 0; k < len; k++) b |= (uint32_t)c[k] << k; r.bits = b;
  cache[key] = r; return r;
}

vector<Run> L, R;  // L.back(): rightmost run left of head; R.back(): leftmost run right of head
// cells in left-to-right order at the top of stack S: for L the top cells are the rightmost ones.
static void raw_push(vector<Run>& S, uint32_t b, int l, uint64_t n) {
  if (!S.empty() && S.back().bits == b && S.back().len == l) { S.back().cnt += n; return; }
  S.push_back({b, (uint8_t)l, n});
}
// try to fold single cells at the top of S into a token
static void fold(vector<Run>& S, bool isL) {
  for (int guard = 0; guard < 4; guard++) {
    bool did = false;
    for (int l = MAXTL; l >= 2 && !did; l--) {
      // collect l cells from single-cell runs at the top
      int got = 0; uint32_t cells[32]; int k = (int)S.size() - 1;
      uint64_t used = 0;
      while (got < l && k >= 0 && S[k].len == 1) {
        uint64_t take = S[k].cnt - (k == (int)S.size() - 1 ? 0 : 0);
        for (uint64_t j = 0; j < take && got < l; j++) cells[got++] = S[k].bits;
        k--;
      }
      (void)used;
      if (got < l) continue;
      // cells[0] is the topmost cell; left-to-right order: for L reverse, for R as is
      uint32_t b = 0;
      for (int j = 0; j < l; j++) { int c = isL ? cells[l - 1 - j] : cells[j]; b |= (uint32_t)c << j; }
      if (!is_token(b, l)) continue;
      // remove l cells
      int rem = l;
      while (rem > 0) { Run& t = S.back(); if ((int)t.cnt <= rem && t.cnt < (uint64_t)1 << 62) { rem -= (int)t.cnt; S.pop_back(); } else { t.cnt -= rem; rem = 0; } }
      raw_push(S, b, l, 1);
      did = true;
    }
    if (!did) break;
  }
}
static void push(vector<Run>& S, bool isL, uint32_t b, int l, uint64_t n) {
  bool uni0 = b == 0, uni1 = b == ((1u << l) - 1);
  if (l > 1 && (uni0 || uni1)) { b = uni1 ? 1 : 0; n *= l; l = 1; }
  if (l == 1 || is_token(b, l)) {
    raw_push(S, b, l, n);
    if (l == 1) fold(S, isL);
    return;
  }
  // a rotation of a token repeated: w^n = head (tok)^(n-1) tail
  if (n >= 2) for (int r = 1; r < l; r++) {
    uint32_t rot = 0; for (int j = 0; j < l; j++) rot |= ((b >> ((j + r) % l)) & 1) << j;
    if (!is_token(rot, l)) continue;
    // left-to-right: cells 0..r-1, then rot^(n-1), then cells r..l-1
    auto pushcells = [&](int from, int to) {  // push cells b[from..to) in stack order
      if (isL) for (int j = from; j < to; j++) push(S, isL, (b >> j) & 1, 1, 1);
      else for (int j = to - 1; j >= from; j--) push(S, isL, (b >> j) & 1, 1, 1);
    };
    if (isL) { pushcells(0, r); raw_push(S, rot, l, n - 1); pushcells(r, l); }
    else { pushcells(r, l); raw_push(S, rot, l, n - 1); pushcells(0, r); }
    return;
  }
  if (n == 1) {
    if (isL) for (int j = 0; j < l; j++) push(S, isL, (b >> j) & 1, 1, 1);
    else for (int j = l - 1; j >= 0; j--) push(S, isL, (b >> j) & 1, 1, 1);
    return;
  }
  raw_push(S, b, l, n);
}


// ---- shift rules: X u^n wL | wR Y -> X wL | wR v^n Y (or the mirror), found by running u wL wR on its own ----
struct ShiftRes { bool ok; uint32_t v; uint64_t steps; };
unordered_map<string, ShiftRes> scache;
static void expand(const vector<Run>& S, int k, bool isL, vector<int>& out) {
  // the top k runs of S as cells left to right
  out.clear();
  if (isL) { for (int i = (int)S.size() - k; i < (int)S.size(); i++) for (uint64_t c = 0; c < S[i].cnt; c++) for (int j = 0; j < S[i].len; j++) out.push_back(cell(S[i], j)); }
  else { for (int i = (int)S.size() - 1; i >= (int)S.size() - k; i--) for (uint64_t c = 0; c < S[i].cnt; c++) for (int j = 0; j < S[i].len; j++) out.push_back(cell(S[i], j)); }
}
static uint64_t cells_of(const vector<Run>& S, int k) { uint64_t t = 0; for (int i = (int)S.size() - k; i < (int)S.size(); i++) { if (S[i].cnt > 16) return 1000; t += S[i].cnt * S[i].len; } return t; }
static ShiftRes shift_sim(int q, int d, bool uInL, const Run& u, const vector<int>& wL, const vector<int>& wR) {
  string key; key += char(q); key += char(d + 1); key += char(uInL); key += char(u.len); key += to_string(u.bits); key += ':';
  for (int c : wL) key += char('0' + c); key += '|'; for (int c : wR) key += char('0' + c);
  auto it = scache.find(key); if (it != scache.end()) return it->second;
  vector<int> s; int lu = u.len;
  if (uInL) { for (int j = 0; j < lu; j++) s.push_back(cell(u, j)); }
  for (int c : wL) s.push_back(c);
  for (int c : wR) s.push_back(c);
  if (!uInL) { for (int j = 0; j < lu; j++) s.push_back(cell(u, j)); }
  int len = s.size(); int p = (uInL ? lu : 0) + wL.size(); int dd = d; int qq = q;
  int target = uInL ? (int)wL.size() : lu + (int)wL.size();
  ShiftRes res{false, 0, 0};
  for (uint64_t n = 1; n <= 4000; n++) {
    int idx = dd == 1 ? p : p - 1;
    if (idx < 0 || idx >= len) break;
    Tr t = T[qq][s[idx]];
    if (t.halt) break;
    s[idx] = t.w;
    if (t.m == dd) p += dd; else dd = -dd;
    qq = t.q;
    if (qq == q && dd == d && p == target) {
      bool ok = true; uint32_t v = 0;
      if (uInL) {
        for (size_t j = 0; j < wL.size() && ok; j++) ok = s[j] == wL[j];
        for (size_t j = 0; j < wR.size() && ok; j++) ok = s[wL.size() + j] == wR[j];
        for (int j = 0; j < lu; j++) v |= (uint32_t)s[wL.size() + wR.size() + j] << j;
      } else {
        for (int j = 0; j < lu; j++) v |= (uint32_t)s[j] << j;
        for (size_t j = 0; j < wL.size() && ok; j++) ok = s[lu + j] == wL[j];
        for (size_t j = 0; j < wR.size() && ok; j++) ok = s[lu + wL.size() + j] == wR[j];
      }
      if (ok) { res = {true, v, n}; break; }
    }
  }
  scache[key] = res; return res;
}
static bool try_shift(int q, int d, u128& steps) {
  vector<int> wL, wR;
  for (int side = 0; side < 2; side++) {
    bool uInL = side == 0;
    vector<Run>& U = uInL ? L : R; vector<Run>& O = uInL ? R : L;
    for (int k = 0; k <= 3 && k < (int)U.size(); k++) {
      const Run& u = U[U.size() - 1 - k];
      if (u.cnt < 2 || u.len > 8) continue;
      if (cells_of(U, k) > 12) break;
      for (int j = 0; j <= 3 && j <= (int)O.size(); j++) {
        if (cells_of(O, j) > 12) break;
        if (uInL) { expand(L, k, true, wL); expand(R, j, false, wR); }
        else { expand(L, j, true, wL); expand(R, k, false, wR); }
        if (wL.size() + wR.size() == 0) continue;
        ShiftRes r = shift_sim(q, d, uInL, u, wL, wR);
        if (!r.ok) continue;
        // apply
        Run uu = u; uint64_t n = uu.cnt;
        vector<Run> above(U.end() - k, U.end()); U.resize(U.size() - k); U.pop_back();
        vector<Run> oth(O.end() - j, O.end()); O.resize(O.size() - j);
        for (auto& a : above) U.push_back(a);
        push(O, !uInL, r.v, uu.len, n);
        for (auto& a : oth) O.push_back(a);
        steps += (u128)r.steps * n;
        return true;
      }
    }
  }
  return false;
}

static void print_tape(u128 steps, int side, int q, int d, int maxruns) {
  char buf[64]; int p = 63; buf[p] = 0; u128 s = steps; do { buf[--p] = '0' + (int)(s % 10); s /= 10; } while (s);
  printf("%s %c %c ", buf + p, side < 0 ? 'L' : 'R', 'A' + q);
  int nr = L.size() + R.size();
  auto pr = [&](const Run& r) { printf("%s", wstr(r.bits, r.len).c_str()); if (r.cnt > 1) printf("^%llu", (unsigned long long)r.cnt); printf(" "); };
  if (nr > maxruns) { printf("(%d runs)\n", nr); return; }
  for (size_t i = 0; i < L.size(); i++) pr(L[i]);
  printf("%s ", d == 1 ? ">" : "<");
  for (size_t i = R.size(); i-- > 0;) pr(R[i]);
  printf("\n");
}

int main(int argc, char** argv) {
  if (argc < 6) { fprintf(stderr, "usage\n"); return 1; }
  const char* M = argv[1];
  NS = (strlen(M) + 1) / 7;
  for (int q = 0; q < NS; q++) for (int b = 0; b < 2; b++) {
    const char* s = M + 7 * q + 3 * b;
    if (s[2] == '-' || s[0] == '-') { T[q][b].halt = true; continue; }
    T[q][b] = {s[0] - '0', s[1] == 'R' ? 1 : -1, s[2] - 'A', false};
  }
  { string t = argv[2]; size_t i = 0;
    while (i < t.size()) { size_t j = t.find(',', i); if (j == string::npos) j = t.size();
      string w = t.substr(i, j - i); uint32_t b = 0; for (size_t k = 0; k < w.size(); k++) b |= (uint32_t)(w[k] - '0') << k;
      if (!w.empty()) { TOK.push_back({b, (int)w.size()}); if ((int)w.size() > MAXTL) MAXTL = w.size(); } i = j + 1; } }
  double maxsteps = atof(argv[3]), maxsec = atof(argv[4]); long maxlines = atol(argv[5]);
  int mode = argc > 6 ? atoi(argv[6]) : 0; int maxruns = argc > 7 ? atoi(argv[7]) : 400;
  uint64_t nshift = 0; int q = 0, d = 1; u128 steps = 0; uint64_t ms = 0; int lastside = 0; long lines = 0;
  clock_t t0 = clock();
  while ((double)steps < maxsteps) {
    vector<Run>& F = d == 1 ? R : L; vector<Run>& B = d == 1 ? L : R;
    if (F.empty()) {
      int side = d;
      if (mode == 1 || side != lastside) { print_tape(steps, side, q, d, maxruns); lastside = side; if (++lines >= maxlines) break; }
      F.push_back({0, 1, 1});
    }
    Run top = F.back();
    Res r = sim(q, top.bits, top.len, d);
    if (r.halt) { // run the halting copy: report
      char buf[64]; int p = 63; buf[p] = 0; u128 s = steps + r.steps; do { buf[--p] = '0' + (int)(s % 10); s /= 10; } while (s);
      printf("HALT at step %s\n", buf + p); return 0;
    }
    ms++;
    if (getenv("DBG") && (double)steps >= atof(getenv("DBG"))) print_tape(steps, 0, q, d, maxruns);
    if ((ms & 0xfffff) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > maxsec) break;
    if (r.far && r.q == q) {
      F.pop_back(); steps += (u128)r.steps * top.cnt; push(B, d == 1, r.bits, top.len, top.cnt); continue;
    }
    if (try_shift(q, d, steps)) { nshift++; continue; }
    if (top.cnt >= 3 && top.len > 1) {
      // try a rotation of the word that crosses
      int found = -1;
      for (int k = 1; k < top.len; k++) {
        uint32_t rot = 0; for (int j = 0; j < top.len; j++) rot |= ((top.bits >> ((j + k) % top.len)) & 1) << j;
        Res rr = sim(q, rot, top.len, d);
        // the rotation only helps if the first cells (in the direction of motion) lead into it in state q
        if (rr.far && rr.q == q && !rr.halt) { found = k; break; }
      }
      if (found > 0) {
        int k = found, l = top.len; uint32_t b = top.bits;
        uint32_t rot = 0; for (int j = 0; j < l; j++) rot |= ((b >> ((j + k) % l)) & 1) << j;
        F.pop_back();
        // left-to-right: b[0..k) rot^(n-1) b[k..l)
        if (d == 1) {  // R stack, top = leftmost; push in reverse order
          for (int j = l - 1; j >= k; j--) raw_push(F, (b >> j) & 1, 1, 1);
          raw_push(F, rot, l, top.cnt - 1);
          for (int j = k - 1; j >= 0; j--) raw_push(F, (b >> j) & 1, 1, 1);
        } else {       // L stack, top = rightmost
          for (int j = 0; j < k; j++) raw_push(F, (b >> j) & 1, 1, 1);
          raw_push(F, rot, l, top.cnt - 1);
          for (int j = k; j < l; j++) raw_push(F, (b >> j) & 1, 1, 1);
        }
        continue;
      }
    }
    // one copy
    if (--F.back().cnt == 0) F.pop_back();
    steps += r.steps;
    if (r.far) push(B, d == 1, r.bits, top.len, 1);
    else { push(F, d != 1, r.bits, top.len, 1); d = -d; }
    q = r.q;
  }
  char buf[64]; int p = 63; buf[p] = 0; u128 s = steps; do { buf[--p] = '0' + (int)(s % 10); s /= 10; } while (s);
  fprintf(stderr, "stopped at step %s, %llu macro steps, %llu shifts, %.1f s\n", buf + p, (unsigned long long)ms, (unsigned long long)nshift, (double)(clock() - t0) / CLOCKS_PER_SEC);
  return 0;
}
