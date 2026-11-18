// rsim.cpp: C++ port of py/rsim.py (same algorithm, same constants, same decisions), for long runs.
//
// The tape is a left rope + buffer + right rope; ropes are stacks of [word, count]; learned transition and periodic
// rules cross copies of a word at once, and sample-level jumps (validated, not proved: see the docstring of
// py/rsim.py) apply many periods of a recurring tape shape at once.  Counts and steps are 128-bit; the program stops
// with OVERFLOW before any count or the step count could pass 2^120.
//
// The one intended difference from the Python program: a sample's signature is a 64-bit hash of a string encoding
// of the shape instead of Python's hash of a tuple (a collision would only make a jump be tried; tryjump still
// compares the counts of n periods).  py/rsim_cmp.py checks that both programs agree exactly (steps, state, jumps,
// rules applied, the whole tape) at a list of step targets.
//
// usage: rsim MACHINE MAXSTEPS [KEEP] [nojumps]       run to MAXSTEPS (a number like 1e15), print a summary
//        rsim MACHINE dump T1,T2,... [KEEP]           after run(T) for each target: steps state jumps nrule tape
//        rsim MACHINE decades SECONDS [KEEP]          run decade after decade (like py/rsim_longrun.py) for a
//                                                   wall-clock budget; one line per decade
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <ctime>
#include <string>
#include <vector>
#include <map>
#include <set>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <algorithm>
#include <functional>
using namespace std;
typedef __int128 I;

static string dec(I v) {
    if (v == 0) return "0";
    bool neg = v < 0; if (neg) v = -v;
    string s; while (v > 0) { s += char('0' + (int)(v % 10)); v /= 10; }
    if (neg) s += '-';
    reverse(s.begin(), s.end()); return s;
}
static const I LIMIT = ((I)1) << 120;
struct Overflow {};
struct Halt {};
static inline void chk(I v) { if (v > LIMIT || v < -LIMIT) throw Overflow(); }
static I floordiv(I a, I b) { I q = a / b; if ((a % b != 0) && ((a < 0) != (b < 0))) q--; return q; }
static I gcdI(I a, I b) { if (a < 0) a = -a; if (b < 0) b = -b; while (b) { I t = a % b; a = b; b = t; } return a; }
static I lcmI(I a, I b) { return a / gcdI(a, b) * b; }

struct Tr { int w, d, s; bool halt; };
static Tr TT[8][2];
static int NS;
static void parse(const string &m) {
    int q = 0; size_t p = 0;
    while (p < m.size()) {
        for (int b = 0; b < 2; b++) {
            if (m[p] == '-') TT[q][b].halt = true;
            else { TT[q][b].halt = false; TT[q][b].w = m[p] - '0'; TT[q][b].d = m[p + 1] == 'R' ? 1 : -1; TT[q][b].s = m[p + 2] - 'A'; }
            p += 3;
        }
        q++; if (p < m.size() && m[p] == '_') p++;
    }
    NS = q;
}

struct Item { string w; I c; bool operator==(const Item &o) const { return c == o.c && w == o.w; } };
typedef vector<Item> Rope;

static string rep(const string &w, I c) { string s; s.reserve(w.size() * (size_t)c); for (I i = 0; i < c; i++) s += w; return s; }
static bool startswith_at(const string &s, const string &w, size_t pos) { return pos <= s.size() && s.compare(pos, w.size(), w) == 0 && pos + w.size() <= s.size(); }

struct Canon { string W; long k; long r; };
static unordered_map<string, Canon> canon_memo;
static const Canon &canon(const string &w) {
    auto it = canon_memo.find(w);
    if (it != canon_memo.end()) return it->second;
    size_t n = w.size(); size_t p = n;
    for (size_t q = 1; q <= n / 2; q++) {
        if (n % q) continue;
        bool ok = true; for (size_t i = q; i < n && ok; i++) if (w[i] != w[i - q]) ok = false;
        if (ok) { p = q; break; }
    }
    string root = w.substr(0, p), dd = root + root;
    size_t r = 0; for (size_t i = 1; i < p; i++) if (dd.compare(i, p, dd, r, p) < 0) r = i;
    Canon c{dd.substr(r, p), (long)(n / p), (long)r};
    if (canon_memo.size() > 4000000) canon_memo.clear();
    return canon_memo.emplace(w, c).first->second;
}

static vector<Item> compress1(const string &s, int minrep = 3, int maxp = 12, int mincover = 6) {
    vector<Item> out; size_t i = 0, n = s.size(), loose = 0;
    while (i < n) {
        long bestc = -1, bp = 0, br = 0;
        for (int p = 1; p <= maxp; p++) {
            if (i + (size_t)p * minrep > n) break;
            string w = s.substr(i, p); long r = 1;
            while (startswith_at(s, w, i + r * p)) r++;
            if (r >= minrep && r * p >= mincover && (bestc < 0 || r * p > bestc)) { bestc = r * p; bp = p; br = r; }
        }
        if (bestc >= 0) {
            long p = bp, r = br;
            Canon cw = canon(s.substr(i, p)); const string &w = cw.W; long o = cw.r;
            if (o) { i += o; r = 1; while (startswith_at(s, w, i + r * p)) r++; }
            if (r >= 2) {
                if (loose < i) out.push_back(Item{s.substr(loose, i - loose), 1});
                out.push_back(Item{w, (I)r}); i += p * r; loose = i;
            } else i++;
        } else i++;
    }
    if (loose < n) out.push_back(Item{s.substr(loose), 1});
    return out;
}
static vector<Item> compress0(const string &s) {
    vector<Item> items = compress1(s); size_t n = items.size();
    if (n < 3) return items;
    vector<Item> out; size_t i = 0;
    while (i < n) {
        size_t hq = 0, hr = 0;
        for (size_t q = 1; q <= 6; q++) {
            if (i + 3 * q > n) break;
            size_t r = 1;
            while (i + (r + 1) * q <= n && equal(items.begin() + i, items.begin() + i + q, items.begin() + i + r * q)) r++;
            if (r >= 3 && (q > 1 || items[i].c == 1)) { hq = q; hr = r; break; }
        }
        if (hq) {
            string X; for (size_t t = i; t < i + hq; t++) X += rep(items[t].w, items[t].c);
            Canon cx = canon(X);
            if (cx.r == 0) out.push_back(Item{cx.W, (I)hr * cx.k});
            else {
                string root = X.substr(0, cx.W.size());
                out.push_back(Item{root.substr(0, cx.r), 1});
                out.push_back(Item{cx.W, (I)hr * cx.k - 1});
                out.push_back(Item{root.substr(cx.r), 1});
            }
            i += hq * hr;
        } else { out.push_back(items[i]); i++; }
    }
    return out;
}
static unordered_map<string, vector<Item>> cmemo;
static vector<Item> compress(const string &s) {
    auto it = cmemo.find(s);
    if (it != cmemo.end()) return it->second;
    vector<Item> r = compress0(s);
    if (cmemo.size() > 2000000) cmemo.clear();
    cmemo[s] = r; return r;
}

// a rule: kind 'T' (one copy, exit state s1) or 'P' (P copies, word O left behind per period)
struct Rule { char kind; int D; string Tt; int P; string O; int s1; string out; I st; };
struct RuleTab { vector<pair<int, unordered_map<string, Rule>>> byD; };   // D in insertion order

struct Sample { uint64_t sig; vector<I> counts; I steps; I lcm; };

struct RSim {
    long KEEP = 1024, TRAIL = 256, TRAILMAX = 1024, K = 10, SCRATCH_STEPS = 400000, MARGIN = 8, BIG = 8, TRAVEL = 48;
    Rope L, R; vector<uint8_t> buf{0}; long h = 0; I base = 0; int s = 0; I steps = 0;
    map<tuple<int, int, string>, RuleTab> rules, prules;
    set<tuple<int, int, string, int, string>> ptried;
    set<tuple<int, int, string, string>> fail;
    bool jumps = true;
    unordered_map<uint64_t, vector<long>> hist; vector<Sample> samples;
    int lastdir = 1; I lastright = 0, lastleft = 0, lcm = 1;
    long njumps = 0, nsamp = 0, nrule = 0, nlearn = 0; I jumped = 0; bool halted = false;

    static string bits(const vector<uint8_t> &v, size_t a, size_t b) { string s; s.reserve(b - a); for (size_t i = a; i < b; i++) s += char('0' + v[i]); return s; }

    // does the string t (the top i items, tape order) start (left) or end (right) with W?  The piece nearest that end
    // is rope[n-i], then rope[n-i+1], ...
    static bool edge_match(const Rope &rope, size_t n, size_t i, bool left, const string &W) {
        size_t need = W.size(), pos = 0;
        for (size_t j = n - i; j < n && pos < need; j++) {
            const string &u = rope[j].w; size_t lu = u.size();
            for (I c = 0; c < rope[j].c && pos < need; c++)
                for (size_t k = 0; k < lu && pos < need; k++, pos++) {
                    char a = left ? u[k] : u[lu - 1 - k];
                    char b = left ? W[pos] : W[need - 1 - pos];
                    if (a != b) return false;
                }
        }
        return pos == need;
    }
    void tidy(Rope &rope, bool left) {
        while (true) {
            size_t n = rope.size(); bool done = true; I tlen = 0;
            for (size_t i = 1; i < min(n, (size_t)9); i++) {
                Item &it = rope[n - i];
                if ((I)it.w.size() * it.c > 4000) break;
                tlen += (I)it.w.size() * it.c;      // t: the top i items as one string (tape order), built only on a match
                const string W = rope[n - i - 1].w;
                if ((I)W.size() <= tlen && W != it.w && edge_match(rope, n, i, left, W)) {
                    string t;
                    for (size_t k = 1; k <= i; k++) { string piece = rep(rope[n - k].w, rope[n - k].c); t = left ? piece + t : t + piece; }
                    string rest = left ? t.substr(W.size()) : t.substr(0, t.size() - W.size());
                    rope.resize(n - i);
                    rope.back().c += 1;
                    if (!rest.empty()) {
                        vector<Item> cs = compress(rest);
                        if (left) for (auto &x : cs) rope.push_back(x);
                        else for (auto x = cs.rbegin(); x != cs.rend(); ++x) rope.push_back(*x);
                    }
                    done = false; break;
                }
            }
            if (!done) continue;
            for (size_t q = 1; q <= 6; q++) {
                if (n >= 3 * q && equal(rope.end() - q, rope.end(), rope.end() - 2 * q) && equal(rope.end() - 2 * q, rope.end() - q, rope.end() - 3 * q)) {
                    string X;
                    if (left) for (size_t t2 = n - q; t2 < n; t2++) X += rep(rope[t2].w, rope[t2].c);
                    else for (size_t t2 = n; t2-- > n - q;) X += rep(rope[t2].w, rope[t2].c);
                    if (X.size() > 4000) continue;
                    rope.resize(n - 3 * q);
                    pushrun_(rope, left, X, 3);
                    done = false; break;
                }
            }
            if (done) return;
        }
    }
    void append(Rope &rope, const Item &it) {
        if (!rope.empty() && rope.back().w == it.w) { rope.back().c += it.c; chk(rope.back().c); }
        else rope.push_back(it);
    }
    void pushstr(Rope &rope, bool left, string str) {
        if (rope.empty()) {
            if (left) { size_t a = str.find('1'); str = a == string::npos ? "" : str.substr(a); }
            else { size_t b = str.rfind('1'); str = b == string::npos ? "" : str.substr(0, b + 1); }
        }
        if (str.empty()) return;
        vector<Item> items = compress(str);
        if (left) for (auto &x : items) append(rope, x);
        else for (auto x = items.rbegin(); x != items.rend(); ++x) append(rope, *x);
        tidy(rope, left);
    }
    void pushrun_(Rope &rope, bool left, const string &O, I J) {
        if (J <= 0) return;
        Canon c = canon(O); size_t p = c.W.size();
        if (c.r == 0) { append(rope, Item{c.W, J * c.k}); tidy(rope, left); return; }
        string root = O.substr(0, p), pre = root.substr(0, c.r), post = root.substr(c.r);
        if (left) { pushstr(rope, left, pre); if (J * c.k > 1) append(rope, Item{c.W, J * c.k - 1}); pushstr(rope, left, post); }
        else { pushstr(rope, left, post); if (J * c.k > 1) append(rope, Item{c.W, J * c.k - 1}); pushstr(rope, left, pre); }
    }
    void pushR(const string &x) { pushstr(R, false, x); }
    void pushL(const string &x) { pushstr(L, true, x); }

    void flush() {
        if (h > 2 * KEEP) {
            long cut = h - KEEP; pushL(bits(buf, 0, cut)); buf.erase(buf.begin(), buf.begin() + cut); h -= cut; base += cut;
        }
        if ((long)buf.size() - h > 2 * KEEP) {
            long cut = h + KEEP; pushR(bits(buf, cut, buf.size())); buf.resize(cut);
        }
    }
    void flush_all() {
        if (h > 0) pushL(bits(buf, 0, min((size_t)h, buf.size())));
        if (h < (long)buf.size()) pushR(bits(buf, max(h, 0L), buf.size()));
        base += h; buf.clear(); h = 0;
    }
    void ensure_behind(int d, long D) {
        while ((long)buf.size() < D) {
            Rope &rope = d < 0 ? R : L; vector<uint8_t> add;
            if (rope.empty()) add.assign(64, 0);
            else {
                Item &it = rope.back(); for (char ch : it.w) add.push_back(ch - '0');
                it.c -= 1; if (it.c == 0) rope.pop_back();
            }
            if (d < 0) buf.insert(buf.end(), add.begin(), add.end());
            else { buf.insert(buf.begin(), add.begin(), add.end()); h += add.size(); base -= add.size(); }
        }
    }
    struct Rec { int s; long steps; long D; };
    void scratch(int st, int d, const vector<uint8_t> &wf, const vector<uint8_t> &tr, long KK, vector<Rec> &recs, vector<vector<uint8_t>> &snaps) {
        long lt = tr.size(), lw = wf.size();
        vector<uint8_t> arr = tr; for (long k = 0; k < KK; k++) arr.insert(arr.end(), wf.begin(), wf.end());
        long pos = lt, nextb = lt + lw, lo = pos, stp = 0;
        snaps.push_back(arr);
        while (stp < SCRATCH_STEPS) {
            if (pos >= nextb) {
                recs.push_back(Rec{st, stp, max(nextb - lw - lo, 0L)}); snaps.push_back(arr);
                if ((long)recs.size() == KK) break;
                lo = pos; nextb += lw;
            }
            if (pos < 0) break;
            const Tr &t = TT[st][arr[pos]];
            if (t.halt) break;
            arr[pos] = t.w; pos += t.d * d; st = t.s; stp++;
            if (pos < lo) lo = pos;
        }
    }
    static string vs(const vector<uint8_t> &v, long a, long b) { string s; for (long i = a; i < b; i++) s += char('0' + v[i]); return s; }
    void addrule(int st, int d, const string &w, int D, const string &Tt, const Rule &rule) {
        auto &tabs = rule.kind == 'P' ? prules : rules;
        RuleTab &rt = tabs[make_tuple(st, d, w)];
        for (auto &pr : rt.byD) if (pr.first == D) { pr.second[Tt] = rule; return; }
        rt.byD.push_back({D, {}}); rt.byD.back().second[Tt] = rule;
    }
    bool learn(int d, bool force, Rule &rule) {
        Rope &rope = d < 0 ? L : R;
        string w = rope.back().w; I c = rope.back().c; int st = s;
        ensure_behind(d, TRAIL);
        vector<uint8_t> tr, wf;
        if (d < 0) { long m = min((long)buf.size(), TRAILMAX); tr.assign(buf.begin(), buf.begin() + m); reverse(tr.begin(), tr.end()); for (auto it = w.rbegin(); it != w.rend(); ++it) wf.push_back(*it - '0'); }
        else { long m = min((long)buf.size(), TRAILMAX); tr.assign(buf.end() - m, buf.end()); for (char ch : w) wf.push_back(ch - '0'); }
        string trk = vs(tr, max(0L, (long)tr.size() - 128), tr.size());
        auto key = make_tuple(st, d, w, trk);
        if (fail.count(key) && !force) return false;
        nlearn++;
        long KK = c < K ? (long)c : K;
        vector<Rec> recs; vector<vector<uint8_t>> snaps;
        scratch(st, d, wf, tr, KK, recs, snaps);
        long lt = tr.size(), lw = wf.size();
        if (recs.empty()) { fail.insert(key); return false; }
        bool have = false;
        if (recs.size() >= 2) {
            vector<int> states{st}; vector<long> stp{0}; vector<long> Ds;
            for (auto &r : recs) { states.push_back(r.s); stp.push_back(r.steps); Ds.push_back(r.D); }
            long fi = -1, fj = -1, fD = 0;
            for (long i = 0; i < (long)recs.size() && fi < 0; i++)
                for (long j = i + 1; j <= (long)recs.size(); j++) {
                    if (states[i] != states[j]) continue;
                    long D = *max_element(Ds.begin() + i, Ds.begin() + j);
                    long bi = lt + i * lw, bj = lt + j * lw;
                    if (D > bi) continue;
                    if (equal(snaps[i].begin() + bi - D, snaps[i].begin() + bi, snaps[j].begin() + bj - D)) { fi = i; fj = j; fD = D; break; }
                }
            if (fi >= 0) {
                long i = fi, j = fj, D = fD, P = j - i, bi = lt + i * lw, bj = lt + j * lw;
                Rule pr; pr.kind = 'P'; pr.D = D; pr.Tt = vs(snaps[i], bi - D, bi); pr.P = P; pr.O = vs(snaps[j], bi - D, bj - D); pr.st = stp[j] - stp[i]; pr.s1 = 0;
                addrule(states[i], d, w, D, pr.Tt, pr);
                if (i == 0) { rule = pr; have = true; }
            }
        }
        if (!have) {
            Rule tr2; tr2.kind = 'T'; tr2.D = recs[0].D; tr2.Tt = vs(tr, lt - tr2.D, lt); tr2.s1 = recs[0].s; tr2.out = vs(snaps[1], lt - tr2.D, lt + lw); tr2.st = recs[0].steps; tr2.P = 0;
            addrule(st, d, w, tr2.D, tr2.Tt, tr2);
            rule = tr2;
        }
        return true;
    }
    const Rule *lookup(map<tuple<int, int, string>, RuleTab> &tabs, int d, const string &w, I c) {
        auto f = tabs.find(make_tuple(s, d, w));
        if (f == tabs.end()) return nullptr;
        for (auto &pr : f->second.byD) {
            int D = pr.first;
            if ((long)buf.size() < D) ensure_behind(d, D);
            string Tt;
            if (D == 0) Tt = "";
            else if (d < 0) { for (long i = D - 1; i >= 0; i--) Tt += char('0' + buf[i]); }
            else Tt = vs(buf, buf.size() - D, buf.size());
            auto r = pr.second.find(Tt);
            if (r != pr.second.end() && (r->second.kind == 'T' || c >= r->second.P)) return &r->second;
        }
        return nullptr;
    }
    bool find(int d, Rule &out) {
        Rope &rope = d < 0 ? L : R;
        string w = rope.back().w; I c = rope.back().c;
        if (c >= 2) { const Rule *r = lookup(prules, d, w, c); if (r) { out = *r; return true; } }
        const Rule *r = lookup(rules, d, w, c);
        if (r && c >= 2) {
            Rule rc = *r;
            auto key = make_tuple(s, d, w, rc.D, rc.Tt);
            if (!ptried.count(key)) {
                ptried.insert(key);
                Rule r2;
                if (learn(d, true, r2) && r2.kind == 'P' && c >= r2.P) { out = r2; return true; }
            }
            out = rc; return true;
        }
        if (r) { out = *r; return true; }
        return false;
    }
    void apply(int d, const Rule &rule) {
        Rope &rope = d < 0 ? L : R;
        long lw = rope.back().w.size(); I c = rope.back().c;
        long D = rule.D; nrule++;
        if (rule.kind == 'P') {
            if (d < 0) { if ((long)buf.size() > D) { pushR(bits(buf, D, buf.size())); buf.resize(D); } }
            else if ((long)buf.size() > D) { long cut = buf.size() - D; pushL(bits(buf, 0, cut)); buf.erase(buf.begin(), buf.begin() + cut); base += cut; }
            I J = c / rule.P;
            if (d < 0) { string Or(rule.O.rbegin(), rule.O.rend()); pushrun_(R, false, Or, J); base -= J * rule.P * lw; h = -1; }
            else { pushrun_(L, true, rule.O, J); base += J * rule.P * lw; h = buf.size(); }
            steps += J * rule.st; chk(steps);
            Rope &rp = d < 0 ? L : R;          // the facing rope (not touched by the pushes above)
            rp.back().c -= J * rule.P; if (rp.back().c == 0) rp.pop_back();
            if (rule.P > 1) lcm = lcmI(lcm, rule.P);
        } else {
            if (d < 0) { buf.insert(buf.begin(), lw, 0);        // buf[:D] = out[::-1] (out has D + lw cells)
                         for (long i = 0; i < D + lw; i++) buf[i] = rule.out[D + lw - 1 - i] - '0';
                         base -= lw; h = -1; }
            else { if (D) buf.resize(buf.size() - D); for (char ch : rule.out) buf.push_back(ch - '0'); h = buf.size(); }
            s = rule.s1; steps += rule.st; chk(steps);
            Rope &rp = d < 0 ? L : R;
            rp.back().c -= 1; if (rp.back().c == 0) rp.pop_back();
        }
    }
    void edge(int d) {
        if (d != lastdir) {
            if (d > 0 && jumps && lastright - lastleft >= TRAVEL) sample();
            lastdir = d;
        }
        if (d > 0) lastright = base + h; else lastleft = base + h;
        Rope &rope = d < 0 ? L : R;
        if (rope.empty()) {
            if (d < 0) { buf.insert(buf.begin(), 64, 0); h += 64; base -= 64; }
            else buf.insert(buf.end(), 64, 0);
            return;
        }
        Rule rule; bool have = find(d, rule);
        if (!have) {
            have = learn(d, false, rule);
            if (have && rule.kind == 'P' && rope.back().c < rule.P) have = false;
        }
        if (have) { apply(d, rule); return; }
        Item &it = rope.back(); vector<uint8_t> add; for (char ch : it.w) add.push_back(ch - '0');
        it.c -= 1; if (it.c == 0) rope.pop_back();
        if (d < 0) { buf.insert(buf.begin(), add.begin(), add.end()); h += add.size(); base -= add.size(); }
        else buf.insert(buf.end(), add.begin(), add.end());
    }
    void run(I maxsteps) {
        while (steps < maxsteps) {
            long n = buf.size(); long hh = h; int st = s; long k = 0;
            I lim = maxsteps - steps; if (lim > 200000) lim = 200000;
            uint8_t *b = buf.data();
            while (0 <= hh && hh < n && k < lim) {
                const Tr &t = TT[st][b[hh]];
                if (t.halt) { h = hh; s = st; steps += k + 1; halted = true; throw Halt(); }
                b[hh] = t.w; hh += t.d; st = t.s; k++;
            }
            h = hh; s = st; steps += k;
            if (hh < 0) edge(-1); else if (hh >= n) edge(1);
            if ((long)buf.size() > 4 * KEEP) flush();
        }
    }
    // ---------------------------------------------------------------- samples and jumps
    struct Ref { int rope; size_t idx; };
    uint64_t signature(vector<Ref> &refs, vector<I> &counts) {
        flush_all();
        string sig; string loose;
        size_t a = 0; while (a < L.size() && L[a].w.find('1') == string::npos) a++;
        long b = R.size(); while (b > 0 && R[R.size() - b].w.find('1') == string::npos) b--;    // Rs = R reversed; Rs[b-1] = R[len-b]
        auto emit_loose = [&]() { if (!loose.empty()) { sig += 'l'; sig += loose; sig += '|'; loose.clear(); } };
        for (size_t i = a; i < L.size(); i++) {
            Item &it = L[i];
            if (it.c >= BIG) { emit_loose(); sig += 'w'; sig += it.w; sig += '|'; refs.push_back(Ref{0, i}); counts.push_back(it.c); }
            else loose += rep(it.w, it.c);
        }
        emit_loose(); sig += 'H'; sig += char('A' + s); sig += '|';
        for (long k = 0; k < b; k++) {
            size_t i = R.size() - 1 - k; Item &it = R[i];
            if (it.c >= BIG) { emit_loose(); sig += 'w'; sig += it.w; sig += '|'; refs.push_back(Ref{1, i}); counts.push_back(it.c); }
            else loose += rep(it.w, it.c);
        }
        emit_loose();
        // FNV-1a then a final mix
        uint64_t hsh = 1469598103934665603ULL; for (unsigned char ch : sig) { hsh ^= ch; hsh *= 1099511628211ULL; }
        hsh ^= hsh >> 29; hsh *= 0xbf58476d1ce4e5b9ULL; hsh ^= hsh >> 32;
        return hsh;
    }
    void sample() {
        vector<Ref> refs; vector<I> counts; uint64_t sig = signature(refs, counts);
        long idx = samples.size(); nsamp++;
        samples.push_back(Sample{sig, counts, steps, lcm}); lcm = 1;
        vector<long> &prev = hist[sig]; prev.push_back(idx);
        vector<long> pv = prev;     // prev[-2:-200:-1]
        int tried = 0;
        long np = pv.size();
        for (long t = np - 2; t >= 0 && t > np - 200; t--) {
            long i = pv[t], P = idx - i;
            if (idx - 2 * P < 0) break;
            if (samples[idx - 2 * P].sig != sig) continue;
            tried++; if (tried > 12) break;
            if (tryjump(idx, P, sig, refs, counts)) return;
        }
    }
    bool tryjump(long idx, long P, uint64_t sig, vector<Ref> &refs, vector<I> &counts) {
        vector<Sample> &S = samples;
        if (idx - 2 * P < 0 || S[idx - 2 * P].sig != sig || S[idx - P].counts.size() != counts.size()) return false;
        vector<I> d(counts.size()); bool any = false;
        for (size_t u = 0; u < counts.size(); u++) { d[u] = counts[u] - S[idx - P].counts[u]; if (d[u]) any = true; }
        if (!any) return false;
        long n = 2; I lc = 1;
        while (true) {
            if (idx - n * P < 0) return false;
            lc = 1; for (long t = 0; t < n * P; t++) lc = lcmI(lc, S[idx - t].lcm);
            if (lc + 1 <= n) break;
            n = (long)(lc + 1);
        }
        for (long t = 1; t <= n; t++) {
            long i0 = idx - t * P;
            if (S[i0].sig != sig || S[i0].counts.size() != counts.size()) return false;
            for (size_t u = 0; u < counts.size(); u++) if (S[i0 + P].counts[u] - S[i0].counts[u] != d[u]) return false;
        }
        for (long t = 0; t < P; t++) for (long u = 1; u < n; u++) if (S[idx - t].sig != S[idx - t - u * P].sig) return false;
        vector<I> e(n); for (long t = 0; t < n; t++) e[t] = S[idx - t * P].steps - S[idx - (t + 1) * P].steps;
        vector<I> f(n - 1); for (long t = 0; t < n - 1; t++) f[t] = e[t] - e[t + 1];
        for (auto x : f) if (x != f[0]) return false;
        bool haveJ = false; I J = 0;
        for (size_t u = 0; u < counts.size(); u++) if (d[u] < 0) {
            I j = floordiv(counts[u] - MARGIN - 2 * lc, -d[u]);
            if (!haveJ || j < J) { J = j; haveJ = true; }
        }
        if (haveJ && J >= 2) {
            for (size_t u = 0; u < refs.size(); u++) { Item &it = refs[u].rope == 0 ? L[refs[u].idx] : R[refs[u].idx]; it.c += J * d[u]; chk(it.c); }
            I add = J * e[0]; chk(add); I tri = J * (J + 1) / 2; chk(tri); I add2 = f[0] * tri; chk(add2);
            steps += add + add2; chk(steps);
            njumps++; jumped += J * P;
            hist.clear(); samples.clear();
            return true;
        }
        if (!haveJ) {
            // Python: J is None -> no jump (nothing shrinks); the rule would repeat forever, but rsim.py does not claim it
        }
        return false;
    }
    string tape_dump() {
        // the whole tape in tape order, as L items | buffer with the head marked | R items (from the head outwards)
        string o;
        for (auto &it : L) { o += it.w; o += '^'; o += dec(it.c); o += ' '; }
        o += "[";
        for (long i = 0; i < (long)buf.size(); i++) { if (i == h) o += '>'; o += char('0' + buf[i]); }
        if (h >= (long)buf.size()) o += '>';
        o += "] ";
        if (h < 0) o += "(h=" + to_string(h) + ") ";
        for (auto it = R.rbegin(); it != R.rend(); ++it) { o += it->w; o += '^'; o += dec(it->c); o += ' '; }
        return o;
    }
};

static I parse_num(const char *a) {
    // 1e15, 2.5e20, or a plain integer
    string s(a); size_t e = s.find_first_of("eE");
    if (e == string::npos) { I v = 0; for (char ch : s) v = v * 10 + (ch - '0'); return v; }
    double m = atof(s.substr(0, e).c_str()); int x = atoi(s.substr(e + 1).c_str());
    I v = 1; while (x > 15) { v *= 10; x--; }
    double mm = m; for (int i = 0; i < x; i++) mm *= 10;
    return (I)mm * v;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: rsim MACHINE MAXSTEPS [KEEP] [nojumps] | rsim MACHINE dump T1,T2,.. [KEEP] | rsim MACHINE decades SECONDS [KEEP]\n"); return 2; }
    string m = argv[1]; parse(m);
    RSim sim;
    string mode = argv[2];
    if (mode == "dump") {
        if (argc > 4) sim.KEEP = atol(argv[4]);
        string ts = argv[3]; size_t p = 0;
        try {
            while (p < ts.size()) {
                size_t q = ts.find(',', p); if (q == string::npos) q = ts.size();
                I t = parse_num(ts.substr(p, q - p).c_str()); p = q + 1;
                sim.run(t);
                printf("T %s steps %s state %c jumps %ld nrule %ld nlearn %ld nsamp %ld tape %s\n", dec(t).c_str(), dec(sim.steps).c_str(), 'A' + sim.s, sim.njumps, sim.nrule, sim.nlearn, sim.nsamp, sim.tape_dump().c_str());
                fflush(stdout);
            }
        } catch (Halt &) { printf("HALT %s\n", dec(sim.steps).c_str()); }
        catch (Overflow &) { printf("OVERFLOW at %s\n", dec(sim.steps).c_str()); }
        return 0;
    }
    if (mode == "decades") {
        if (argc > 4) sim.KEEP = atol(argv[4]); else sim.KEEP = 32;
        double budget = atof(argv[3]); time_t t0 = time(0);
        // like py/rsim_longrun.py, but stopping between run() calls once the budget is spent: run in chunks
        I target = 1000000; int e = 6;
        try {
            while (difftime(time(0), t0) < budget) {
                // advance towards 10^e in slices so the budget is respected
                while (sim.steps < target && difftime(time(0), t0) < budget) {
                    I slice = sim.steps + 2000000000LL; if (slice > target) slice = target;
                    sim.run(slice);
                }
                if (sim.steps >= target) {
                    printf("decade %d steps %s digits %zu sec %.0f jumps %ld samples %ld nL %zu nR %zu\n", e, dec(sim.steps).c_str(), dec(sim.steps).size(), difftime(time(0), t0), sim.njumps, sim.nsamp, sim.L.size(), sim.R.size());
                    fflush(stdout);
                    int dg = dec(sim.steps).size(); e = max(e + 1, dg);
                    if (e > 36) { printf("STOP: 10^37 is the limit of this program\n"); break; }
                    target = 1; for (int i = 0; i < e; i++) target *= 10;
                }
            }
            printf("END open steps %s digits %zu sec %.0f jumps %ld\n", dec(sim.steps).c_str(), dec(sim.steps).size(), difftime(time(0), t0), sim.njumps);
        } catch (Halt &) { printf("HALT %s\n", dec(sim.steps).c_str()); }
        catch (Overflow &) { printf("OVERFLOW at steps %s digits %zu\n", dec(sim.steps).c_str(), dec(sim.steps).size()); }
        return 0;
    }
    I mx = parse_num(argv[2]);
    if (argc > 3) sim.KEEP = atol(argv[3]);
    if (argc > 4 && string(argv[4]) == "nojumps") sim.jumps = false;
    try { sim.run(mx); printf("running %s\n", dec(sim.steps).c_str()); }
    catch (Halt &) { printf("halted %s\n", dec(sim.steps).c_str()); }
    catch (Overflow &) { printf("OVERFLOW at %s\n", dec(sim.steps).c_str()); }
    printf("rules applied %ld learn calls %ld jumps %ld\n", sim.nrule, sim.nlearn, sim.njumps);
    return 0;
}
