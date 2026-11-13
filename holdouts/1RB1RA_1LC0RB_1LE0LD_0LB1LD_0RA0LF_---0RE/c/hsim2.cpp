// hsim2: exact accelerated simulator for a 2-symbol TM from blank tape.
//
// The tape is cut into K-cell blocks, each side of the head run-length coded (a "macro machine", as bbtools.macro).
// At every turn-around of the head (a sample) the shape (state, direction, block sequence) is recorded with its run
// counts.  When the same shape appears three times with constant count increments, a candidate cycle is found; it
// is then *verified symbolically*: the macro steps of one cycle are re-run with the counts of the changing (and the
// long) runs replaced by v_i + T_i, v_i >= 0 free variables (affine counts).  The symbolic run must never need to
// know whether a count with a variable is 0 (a pop leaves the constant part >= 1), and must end, after the same
// number of macro steps, in the same shape with every count moved by its increment.  Then the cycle holds for all
// v >= 0, the steps of a cycle are an affine form S(v), and k cycles are applied at once with their exact step sum.
// So the result is exact given the macro machine (which is the plain machine, block for block); nothing is
// extrapolated without a proof of this kind.  Verified rules are cached by shape and reused.
//
// usage: hsim2 MACHINE K MAXSTEPS MAXSECONDS THR [statefile_in|-] [statefile_out]
//   prints, at left-end turn-arounds, a line each time the skeleton (canonical blocks of runs with count >= THR)
//   changes:  steps state dir secs jumps | left runs (far end first) | right runs (head side first)
//   with LEVELS=1 in the environment it also prints a line "LV steps state | tape" for each level: the tape at a
//   turn-around while the block of `01111` words is at its longest (py/lvx.py reads these lines)
#include <bits/stdc++.h>
using namespace std;
typedef __int128 i128; typedef long long ll; typedef unsigned long long u64;
int K; int NW[6][2], MV[6][2], NS[6][2];
struct Res { int halt; int q; u64 y; int d; ll n; };
struct PH { size_t operator()(const pair<u64,int>& p) const { return p.first * 0x9E3779B97F4A7C15ULL ^ p.second; } };
unordered_map<pair<u64,int>, Res, PH> cache;
Res trans(int q, u64 x, int d) {
  u64 key = x * 16 + (q << 1) + (d == 1); key ^= (u64)x >> 60 << 3;
  pair<u64,int> pk(x, q * 2 + (d == 1)); auto it = cache.find(pk); if (it != cache.end()) return it->second;
  Res r; int i = d == 1 ? 0 : K - 1; ll n = 0; u64 c = x;
  while (true) {
    if (i < 0 || i >= K) { r = {0, q, c, i >= K ? 1 : -1, n}; break; }
    int b = (c >> i) & 1;
    if (NS[q][b] < 0) { r = {1, q, c, 0, n + 1}; break; }
    if (n > 1000000) { fprintf(stderr, "loop in block\n"); exit(2); }
    if (NW[q][b]) c |= (1ULL << i); else c &= ~(1ULL << i);
    i += MV[q][b]; q = NS[q][b]; n++;
  }
  cache[pk] = r; return r;
}
string i128s(i128 v) { if (v == 0) return "0"; string s; bool neg = v < 0; if (neg) v = -v; while (v) { s += char('0' + (int)(v % 10)); v /= 10; } if (neg) s += '-'; reverse(s.begin(), s.end()); return s; }

// ---------------------------------------------------------------- concrete macro machine
struct Run { u64 x; ll c; };
vector<Run> L, R;
int st = 0, dir = 1; i128 steps = 0; ll pos = 0; ll msteps = 0; bool halted = false;
void push(vector<Run>& s, u64 x, ll c) { if (s.size() > 1 && s.back().x == x) s.back().c += c; else s.push_back({x, c}); }
bool step() {
  vector<Run>& F = dir == 1 ? R : L; vector<Run>& B = dir == 1 ? L : R;
  u64 x = F.back().x;
  if (F.size() > 1) { if (--F.back().c == 0) F.pop_back(); }
  Res r = trans(st, x, dir);
  if (r.halt) { halted = true; steps += r.n; return false; }
  msteps++;
  if (r.q == st && r.d == dir) {
    ll c = 1; if (F.size() > 1 && F.back().x == x) { c += F.back().c; F.pop_back(); }
    steps += (i128)c * r.n; push(B, r.y, c); pos += (ll)dir * c * K;
  } else {
    steps += r.n; if (r.d == dir) pos += (ll)dir * K;
    push(r.d == 1 ? L : R, r.y, 1);
  }
  st = r.q; dir = r.d; return true;
}

// ---------------------------------------------------------------- symbolic macro machine
const int MAXV = 16;
struct Lin { ll a[MAXV]; ll k; };
int NVAR;
Lin lc(ll k) { Lin l; memset(l.a, 0, sizeof l.a); l.k = k; return l; }
Lin ladd(const Lin& x, const Lin& y) { Lin r; for (int i = 0; i < NVAR; i++) r.a[i] = x.a[i] + y.a[i]; for (int i = NVAR; i < MAXV; i++) r.a[i] = 0; r.k = x.k + y.k; return r; }
Lin lmul(const Lin& x, ll m) { Lin r; for (int i = 0; i < MAXV; i++) r.a[i] = x.a[i] * m; r.k = x.k * m; return r; }
bool lhasvar(const Lin& x) { for (int i = 0; i < NVAR; i++) if (x.a[i]) return true; return false; }
bool leq(const Lin& x, const Lin& y) { if (x.k != y.k) return false; for (int i = 0; i < NVAR; i++) if (x.a[i] != y.a[i]) return false; return true; }
struct SRun { u64 x; Lin c; };
struct SCfg { vector<SRun> L, R; int st, dir; Lin steps; };
bool maybe0(const Lin& c) { return c.k < 1 && lhasvar(c); }
// push block x (count c) onto stack s; returns false if the result depends on whether a maybe-empty top run is empty
bool spush(vector<SRun>& s, u64 x, const Lin& c) {
  if (s.size() > 1 && s.back().x == x) { s.back().c = ladd(s.back().c, c); return true; }
  if (s.size() > 1 && maybe0(s.back().c)) {
    // with the top run empty, x would land on the run below
    if (s.size() > 2 && s[s.size() - 2].x == x) return false;
  }
  s.push_back({x, c}); return true;
}
// one symbolic macro step; returns 0 ok, 1 undecidable/halt
int sstep(SCfg& g) {
  vector<SRun>& F = g.dir == 1 ? g.R : g.L; vector<SRun>& B = g.dir == 1 ? g.L : g.R;
  if (F.size() > 1 && maybe0(F.back().c)) { if (getenv("DBGV")) { fprintf(stderr,"  maybe0 read: st %d dir %d top count k=%lld vars:", g.st, g.dir, F.back().c.k); for(int i=0;i<NVAR;i++) fprintf(stderr," %lld",F.back().c.a[i]); fprintf(stderr,"\n"); } return 1; }    // which block is read depends on a variable
  u64 x = F.back().x;
  if (F.size() > 1) {
    Lin& c = F.back().c;
    c.k -= 1;
    if (!lhasvar(c) && c.k == 0) F.pop_back();
  }
  Res r = trans(g.st, x, g.dir);
  if (r.halt) return 1;
  if (r.q == g.st && r.d == g.dir) {
    Lin c = lc(1);
    if (F.size() > 1 && F.back().x == x) { c = ladd(c, F.back().c); F.pop_back(); }
    else if (F.size() > 1 && maybe0(F.back().c)) return 1;
    g.steps = ladd(g.steps, lmul(c, r.n)); if (!spush(B, r.y, c)) return 1;
  } else {
    g.steps = ladd(g.steps, lc(r.n));
    if (!spush(r.d == 1 ? g.L : g.R, r.y, lc(1))) return 1;
  }
  g.st = r.q; g.dir = r.d; return 0;
}

void printtape(FILE* f);
// ---------------------------------------------------------------- samples, rules, jumps
struct Snap { vector<ll> c; i128 s; ll p; ll ms; };
struct VH { size_t operator()(const vector<u64>& v) const { uint64_t h = 1469598103934665603ULL; for (auto x : v) { h ^= x; h *= 1099511628211ULL; h ^= h >> 29; } return h; } };
struct Rule { vector<ll> d; vector<int> var; vector<ll> T; vector<ll> cst; Lin S; ll dpos; ll ms; };
unordered_map<vector<u64>, vector<Snap>, VH> hist;
unordered_map<vector<u64>, vector<Rule>, VH> rules;
unordered_map<vector<u64>, pair<vector<ll>, ll>, VH> failed; unordered_map<vector<u64>, ll, VH> failn;
ll jumps = 0, nrules = 0, nfail = 0; ll why[8]; ll margin = 2; ll LONG = 16;
vector<u64> keyv() { vector<u64> k; k.push_back(st * 2 + (dir == 1)); for (size_t i = 1; i < L.size(); i++) k.push_back(L[i].x); k.push_back(~0ULL); for (size_t i = 1; i < R.size(); i++) k.push_back(R[i].x); return k; }
vector<ll> countsv() { vector<ll> c; for (size_t i = 1; i < L.size(); i++) c.push_back(L[i].c); for (size_t i = 1; i < R.size(); i++) c.push_back(R[i].c); return c; }

// try to verify a rule from the current concrete configuration: runs with var[i]>=0 get count v + T[i]
bool verify(const vector<ll>& d, const vector<int>& var, const vector<ll>& T, ll ms, Lin& S) {
  SCfg g; g.st = st; g.dir = dir; g.steps = lc(0);
  size_t nl = L.size() - 1;
  vector<ll> c = countsv();
  auto mk = [&](size_t i) { Lin l = lc(var[i] >= 0 ? T[i] : c[i]); if (var[i] >= 0) l.a[var[i]] = 1; return l; };
  g.L.push_back({0, lc(1)}); g.R.push_back({0, lc(1)});
  for (size_t i = 1; i < L.size(); i++) g.L.push_back({L[i].x, mk(i - 1)});
  for (size_t i = 1; i < R.size(); i++) g.R.push_back({R[i].x, mk(nl + i - 1)});
  for (ll j = 0; j < ms; j++) { int e = sstep(g); if (e) { why[0]++; if (getenv("DBGV") && why[0] < 20) fprintf(stderr, "fail at %lld/%lld code %d steps %s\n", j, ms, e, i128s(steps).c_str()); return false; } }
  // compare
  if (g.st != st || g.dir != dir || g.L.size() != L.size() || g.R.size() != R.size()) { why[1]++; return false; }
  for (size_t i = 1; i < L.size(); i++) { if (g.L[i].x != L[i].x) return false; Lin e = mk(i - 1); e.k += d[i - 1]; if (!leq(e, g.L[i].c)) { why[2]++; return false; } }
  for (size_t i = 1; i < R.size(); i++) { if (g.R[i].x != R[i].x) return false; Lin e = mk(nl + i - 1); e.k += d[nl + i - 1]; if (!leq(e, g.R[i].c)) { why[3]++; return false; } }
  S = g.steps; return true;
}
// does rule apply at current counts?  returns max cycles (>=1) or 0
ll applicable(const Rule& r, const vector<ll>& c) {
  ll k = -1; bool shr = false;
  for (size_t i = 0; i < c.size(); i++) {
    if (r.var[i] < 0) { if (c[i] != r.cst[i]) return 0; continue; }
    if (c[i] < r.T[i]) return 0;
    if (r.d[i] < 0) { ll room = (c[i] - r.T[i]) / (-r.d[i]) + 1; if (!shr || room < k) k = room; shr = true; }
  }
  if (!shr) return LLONG_MAX / 4;
  return k;
}
void applyRule(const Rule& r, ll k) {
  vector<ll> c = countsv();
  i128 tot = (i128)k * r.S.k;
  for (size_t i = 0; i < c.size(); i++) if (r.var[i] >= 0) {
    i128 s = r.S.a[r.var[i]]; if (!s) continue;
    tot += s * ((i128)k * (c[i] - r.T[i]) + (i128)r.d[i] * k * (k - 1) / 2);
  }
  size_t j = 0;
  for (size_t i = 1; i < L.size(); i++, j++) L[i].c += k * r.d[j];
  for (size_t i = 1; i < R.size(); i++, j++) R[i].c += k * r.d[j];
  steps += tot; pos += k * r.dpos; jumps++; if (getenv("DBGJ")) fprintf(stderr, "J %s %lld %s ms=%lld\n", i128s(steps - tot).c_str(), k, i128s(steps).c_str(), r.ms);
}
i128 maxsteps;
ll capk(const Rule& r, ll k) {  // do not pass maxsteps by much: cap k (binary search on total)
  return k;
}
void sample() {
  auto key = keyv();
  vector<ll> c = countsv();
  auto rit = rules.find(key);
  if (rit != rules.end()) {
    for (auto& r : rit->second) {
      ll k = applicable(r, c);
      if (k >= 2) {
        if (k > (ll)1e15) k = (ll)1e15;
        applyRule(r, k); hist.erase(key); return;
      }
    }
  }
  if (hist.size() > 100000) hist.clear();
  auto& h = hist[key];
  h.push_back({c, steps, pos, msteps}); if (h.size() > 3) h.erase(h.begin());
  if (h.size() < 3) return;
  size_t n = c.size(); vector<ll> d(n); bool any = false;
  for (size_t i = 0; i < n; i++) { d[i] = h[1].c[i] - h[0].c[i]; if (h[2].c[i] - h[1].c[i] != d[i]) return; if (d[i]) any = true; }
  if (!any) return;
  ll ms = h[2].ms - h[1].ms; if (ms != h[1].ms - h[0].ms) return;
  ll dpos = h[2].p - h[1].p;
  { // worth it only if a few cycles fit
    for (size_t i = 0; i < n; i++) if (d[i] < 0 && c[i] < 6 * (-d[i]) + 2) return;
  }
  { auto fit = failed.find(key); if (fit != failed.end() && fit->second.first == d) { if (--fit->second.second > 0) return; } }
  // variables: changing runs and long runs
  vector<int> var(n, -1); int nv = 0;
  for (size_t i = 0; i < n; i++) if (d[i] || c[i] >= LONG) { if (nv >= MAXV) return; var[i] = nv++; }
  NVAR = nv;
  // first try small thresholds, then the jump's own
  Rule r; r.d = d; r.var = var; r.cst = c; r.dpos = dpos; r.ms = ms;
  bool ok = false;
  for (int attempt = 0; attempt < 3 && !ok; attempt++) {
    vector<ll> T(n, 0);
    for (size_t i = 0; i < n; i++) if (var[i] >= 0) {
      ll base = attempt == 0 ? 2 * llabs(d[i]) + 2 : attempt == 1 ? 8 * llabs(d[i]) + 8 : 0;
      if (attempt == 2) base = c[i] - 2 * llabs(d[i]) * margin;  // close to the present value
      T[i] = min(c[i], max(base, d[i] < 0 ? -d[i] : 0LL));
      if (T[i] < 1) T[i] = 1;
    }
    Lin S;
    if (verify(d, var, T, ms, S)) { r.T = T; r.S = S; ok = true; }
  }
  if (!ok) { ll& fn = failn[key]; fn = fn ? 2 * fn : 4; if (fn > 4096) fn = 4096; failed[key] = {d, fn}; if (failed.size() > 200000) { failed.clear(); failn.clear(); } nfail++; if (getenv("DBGF") && nfail % 100000 == 1) { fprintf(stderr, "FAIL at %s ms=%lld st=%d dir=%d\n c:", i128s(steps).c_str(), ms, st, dir); for (size_t i = 0; i < n; i++) fprintf(stderr, " %lld(%+lld)", c[i], d[i]); fprintf(stderr, "\n tape:"); printtape(stderr); fprintf(stderr, "\n"); } return; }
  nrules++;
  { auto& rv = rules[key]; rv.push_back(r); if (rv.size() > 6) rv.erase(rv.begin()); if (rules.size() > 500000) rules.clear(); }
  ll k = applicable(r, c); if (getenv("DBGR") && nrules < 30) { fprintf(stderr, "R k=%lld ms=%lld:", k, ms); for (size_t i = 0; i < n; i++) fprintf(stderr, " %lld(%+lld,T%lld,v%d)", c[i], d[i], r.T[i], var[i]); fprintf(stderr, "\n"); }
  if (k >= 2) { if (k > (ll)1e15) k = (ll)1e15; applyRule(r, k); hist.erase(key); }
}
string bits(u64 x) { string s; for (int i = 0; i < K; i++) s += char('0' + ((x >> i) & 1)); return s; }
u64 canon(u64 x) { u64 best = x; u64 m = (K == 64) ? ~0ULL : ((1ULL << K) - 1); for (int r = 1; r < K; r++) { u64 y = ((x >> r) | (x << (K - r))) & m; best = min(best, y); } return best; }
void printtape(FILE* f) {
  for (size_t i = 1; i < L.size(); i++) fprintf(f, " %s:%lld", bits(L[i].x).c_str(), L[i].c);
  fprintf(f, " |"); for (size_t i = R.size() - 1; i >= 1; i--) fprintf(f, " %s:%lld", bits(R[i].x).c_str(), R[i].c);
}
void save(const char* fn) {
  FILE* f = fopen(fn, "w");
  fprintf(f, "%s %d %d %lld %lld %lld %zu %zu\n", i128s(steps).c_str(), st, dir, pos, msteps, jumps, L.size(), R.size());
  for (auto& r : L) fprintf(f, "%llu %lld\n", r.x, r.c);
  for (auto& r : R) fprintf(f, "%llu %lld\n", r.x, r.c);
  fclose(f);
}
void load(const char* fn) {
  FILE* f = fopen(fn, "r"); char sb[64]; size_t nl, nr;
  if (fscanf(f, "%63s %d %d %lld %lld %lld %zu %zu", sb, &st, &dir, &pos, &msteps, &jumps, &nl, &nr) != 8) exit(3);
  steps = 0; for (char* p = sb; *p; p++) steps = steps * 10 + (*p - '0');
  L.clear(); R.clear();
  for (size_t i = 0; i < nl; i++) { Run r; if (fscanf(f, "%llu %lld", &r.x, &r.c) != 2) exit(3); L.push_back(r); }
  for (size_t i = 0; i < nr; i++) { Run r; if (fscanf(f, "%llu %lld", &r.x, &r.c) != 2) exit(3); R.push_back(r); }
  fclose(f);
}
bool LV; ll maxc = 20; u64 lvc; string pend;
int main(int argc, char** argv) {
  if (argc < 6) { fprintf(stderr, "usage: hsim2 MACHINE K MAXSTEPS MAXSECONDS THR [in|-] [out]\n"); return 1; }
  const char* M = argv[1]; K = atoi(argv[2]); long double maxs = strtold(argv[3], 0); double maxt = atof(argv[4]); ll thr = atoll(argv[5]);
  for (int s = 0; s < 6; s++) for (int r = 0; r < 2; r++) { const char* t = M + 7 * s + 3 * r; if (t[2] == '-') { NS[s][r] = -1; continue; } NW[s][r] = t[0] - '0'; MV[s][r] = t[1] == 'R' ? 1 : -1; NS[s][r] = t[2] - 'A'; }
  L.push_back({0, 1}); R.push_back({0, 1});
  LV = getenv("LEVELS") != 0; { u64 x = 0; const char* w = "01111"; for (int i = 0; i < K; i++) if (w[i % 5] == '1') x |= 1ULL << i; lvc = canon(x); }
  if (argc > 6 && strcmp(argv[6], "-")) load(argv[6]);
  maxsteps = (i128)maxs; auto t0 = chrono::steady_clock::now(); int lastdir = dir; vector<u64> prevsk; bool first = true; ll samples = 0;
  while (steps < maxsteps) {
    if (!step()) { printf("HALT %s\n", i128s(steps).c_str()); printf("TAPE %c %d |", 'A' + st, dir); printtape(stdout); printf("\n"); return 0; }
    if (dir != lastdir) {
      lastdir = dir; samples++;
      if (L.size() <= 3 && dir == 1 && (L.size() < 2 || L[1].c < thr) && (L.size() < 3 || L[2].c < thr)) {
        vector<u64> sk; for (size_t i = 1; i < L.size(); i++) if (L[i].c >= thr) sk.push_back(canon(L[i].x)); sk.push_back(~0ULL);
        for (size_t i = 1; i < R.size(); i++) if (R[i].c >= thr) sk.push_back(canon(R[i].x));
        if (first || sk != prevsk) {
          first = false; prevsk = sk;
          double el = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
          printf("%s %c %d %.0f %lld |", i128s(steps).c_str(), 'A' + st, dir, el, jumps); printtape(stdout); printf("\n"); fflush(stdout);
        }
      }
      if (LV) {
        ll cur = -1;
        for (size_t i = 1; i < L.size(); i++) if (canon(L[i].x) == lvc && L[i].c > cur) cur = L[i].c;
        if (cur >= maxc && cur >= 20 && (cur > maxc || !pend.empty())) {
          maxc = cur; pend = "LV " + i128s(steps) + " " + char('A' + st) + " |";
          char buf[64];
          for (size_t i = 1; i < L.size(); i++) { snprintf(buf, 64, " %s:%lld", bits(L[i].x).c_str(), L[i].c); pend += buf; }
          pend += " |"; for (size_t i = R.size() - 1; i >= 1; i--) { snprintf(buf, 64, " %s:%lld", bits(R[i].x).c_str(), R[i].c); pend += buf; }
        } else if (cur < maxc - 1) { if (!pend.empty()) { printf("%s\n", pend.c_str()); fflush(stdout); pend.clear(); } maxc = cur < 20 ? 20 : cur; }
      }
      sample();
      if ((samples & 1023) == 0) { double el = chrono::duration<double>(chrono::steady_clock::now() - t0).count(); if (el > maxt) break; }
    }
  }
  printf("END %s msteps=%lld jumps=%lld rules=%lld fails=%lld why=%lld,%lld,%lld,%lld\n", i128s(steps).c_str(), msteps, jumps, nrules, nfail, why[0],why[1],why[2],why[3]);
  printf("TAPE %c %d |", 'A' + st, dir); printtape(stdout); printf("\n");
  if (argc > 7) save(argv[7]);
}
