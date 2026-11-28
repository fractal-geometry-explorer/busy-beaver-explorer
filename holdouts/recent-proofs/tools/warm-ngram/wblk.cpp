// wblk.cpp: a re-implementation of busycoq's CPS_LRU and RWL_mod deciders (verify/CTL.v on the BB6 branch: the
// generic CTL search over the block machine BlockTMFromDHTM, with the CPS_LRU or RWL_mod automaton on each side),
// with the start time simT as the main knob.  busycoq's own deciders take simT too (usually 1001); this tool is for
// trying them from much later starts, e.g. on open holdouts whose transition table busycoq decides from another start
// state.
//
//   wblk MACHINE CPS simT bsz bmaxT len1 len2 len3 LRU_n [-S maxS] [-C maxConfigs]
//   wblk MACHINE RWL simT bsz bmaxT mnc mod len1 len2   [-S maxS] [-C maxConfigs]
//
// (the same parameters, in the same order, as busycoq's CPS_LRU simT maxT maxS bsz bmaxT len1 len2 len3 LRU_n and
// RWL_mod simT maxT maxS bsz bmaxT mnc mod_ len1 len2, without maxT and maxS.)
// Output: "RESULT configs syms lstates rstates", RESULT one of NONHALT, UNKNOWN (abstract halt or block timeout),
// LIMIT, HALT (the machine halted within simT steps).
#include <bits/stdc++.h>
using namespace std;

struct Tr { int w, d, s; bool halt; };
static Tr T[8][2];
static void parse(const string &m) {
    vector<string> rows; string cur;
    for (char c : m) { if (c == '_') { rows.push_back(cur); cur.clear(); } else cur += c; }
    rows.push_back(cur);
    for (size_t q = 0; q < rows.size(); q++) for (int b = 0; b < 2; b++) {
        string t = rows[q].substr(3 * b, 3);
        if (t[2] < 'A' || t[2] > 'Z') T[q][b] = {0, 0, 0, true}; else T[q][b] = {t[0] - '0', t[1] == 'R', t[2] - 'A', false};
    }
}
struct VH { size_t operator()(const vector<int> &v) const { size_t x = 1469598103u; for (int a : v) x = x * 1000003u + a + 1; return x; } };

// ---- block symbols: list of bits, nearest-to-head first; id 0 = nil (the blank block) ----
static vector<vector<int>> syms; static unordered_map<vector<int>, int, VH> symid;
static int maxS = 3200, bsz; static long long bmaxT; static bool overflow = false;
static int sym_of(const vector<int> &v) {
    auto it = symid.find(v); if (it != symid.end()) return it->second;
    if ((int)syms.size() >= maxS) { overflow = true; return -1; }
    int id = syms.size(); syms.push_back(v); symid[v] = id; return id;
}
static bool is_s0(int y) { for (int b : syms[y]) if (b) return false; return true; }

// block step: state q facing sgn reads block y. Returns false on halt or timeout.
struct BRes { int y, d, q; };
static unordered_map<long long, pair<bool, BRes>> bcache;
static bool block_step(int q, int sgn, int y, BRes &out) {
    long long key = ((long long)y * 8 + q) * 2 + sgn;
    auto it = bcache.find(key); if (it != bcache.end()) { out = it->second.second; return it->second.first; }
    vector<int> r = syms[y]; if (r.empty()) r.assign(bsz, 0);
    vector<int> l;   // DH: r = front (nearest first, as stacks we keep nearest at back)
    reverse(r.begin(), r.end());
    int s = q, d = sgn; long long steps = 0; bool ok = true;
    // first bounded step must succeed, then up to bmaxT more
    while (true) {
        if (r.empty()) break;
        int m = r.back(); Tr tr = T[s][m];
        if (tr.halt) { ok = false; break; }
        if (steps > bmaxT) { ok = false; break; }
        r.pop_back();
        if (tr.d == d) l.push_back(tr.w);
        else { r.push_back(tr.w); swap(l, r); }
        s = tr.s; d = tr.d; steps++;
    }
    BRes res{0, 0, 0};
    if (ok) { vector<int> v(l.rbegin(), l.rend()); int id = sym_of(v); if (id < 0) ok = false; else res = {id, d, s}; }
    bcache[key] = {ok, res}; out = res; return ok;
}

// ---- side automata ----
static int mode; // 0 = CPS_LRU, 1 = RWL_mod
static int len1, len2, len3, LRUn, mnc, mod_;
static vector<int> upd_skipn_LRU(int n1, int n2, int lrun, const vector<int> &ls) {
    if ((int)ls.size() <= n1) return ls;
    vector<int> out(ls.begin(), ls.begin() + n1);
    int hd = ls[n1]; vector<int> t; int n = lrun; bool removed = false;
    for (size_t i = n1 + 1; i < ls.size(); i++) {
        if (!removed && ls[i] == hd) { if (n == 0) { removed = true; continue; } n--; }
        t.push_back(ls[i]);
    }
    out.push_back(hd); int room = n2 - 1;
    for (int i = 0; i < (int)t.size() && i < room; i++) out.push_back(t[i]);
    if (n2 == 0) out.pop_back();
    return out;
}
// CPS state encoding: x12 elements, then -1, then x3 elements. RWL: triples (sym, n, m) flattened.
static vector<int> trans_state(const vector<int> &x, int y) {
    if (mode == 0) {
        size_t sep = find(x.begin(), x.end(), -1) - x.begin();
        vector<int> x12(x.begin(), x.begin() + sep), x3;
        if (sep < x.size()) x3.assign(x.begin() + sep + 1, x.end());
        if (x12.empty() && x3.empty() && is_s0(y)) return {};
        if ((int)x3.size() < len3) x3.insert(x3.begin(), y);
        else { vector<int> t; t.push_back(y); t.insert(t.end(), x12.begin(), x12.end()); x12 = upd_skipn_LRU(len1, len2, LRUn, t); }
        vector<int> o = x12; o.push_back(-1); o.insert(o.end(), x3.begin(), x3.end()); return o;
    } else {
        if (x.empty()) { if (is_s0(y)) return {}; return {y, 1, 1}; }
        vector<int> o;
        if (x[0] == y) { o = x; o[1] = o[1] < mnc ? o[1] + 1 : mnc; o[2] = (o[2] + 1) % mod_; }
        else { o = {y, 1, 1}; o.insert(o.end(), x.begin(), x.end()); }
        // limit_length len1 len2 on the list of triples
        int k = o.size() / 3;
        if (k > len1) { int tail = k - len1; if (tail > len2) o.erase(o.begin() + 3 * len1, o.begin() + 3 * len1 + 3); }
        return o;
    }
}
struct DFA {
    vector<vector<int>> st; unordered_map<vector<int>, int, VH> sid;
    unordered_map<long long, int> trans; vector<vector<pair<int,int>>> preds; vector<vector<int>> idx;
    int get_state(const vector<int> &v) {
        auto it = sid.find(v); if (it != sid.end()) return it->second;
        int id = st.size(); st.push_back(v); sid[v] = id; preds.emplace_back(); idx.emplace_back(); return id;
    }
};
static DFA D[2];
struct Cfg { int f, b, s, sgn; };
static vector<Cfg> cfgs; static unordered_map<long long, int> cfgid;
static deque<pair<int, pair<int,int>>> work;
static long long maxC = 20000000;
static void add_cfg(const Cfg &c) {
    long long k = (((long long)c.f * 50000000LL + c.b) * 8 + c.s) * 2 + c.sgn;
    if (cfgid.count(k)) return;
    int id = cfgs.size(); cfgs.push_back(c); cfgid[k] = id;
    D[c.sgn].idx[c.f].push_back(id);
    for (auto &p : D[c.sgn].preds[c.f]) work.push_back({id, p});
}
static int trans_add(int side, int x, int y) {
    DFA &A = D[side]; long long key = ((long long)x << 20) | y;
    auto it = A.trans.find(key); if (it != A.trans.end()) return it->second;
    int z = A.get_state(trans_state(A.st[x], y));
    A.trans[key] = z; A.preds[z].push_back({x, y});
    for (int c : A.idx[z]) if (cfgs[c].sgn == side) work.push_back({c, {x, y}});
    return z;
}

int main(int argc, char **argv) {
    if (argc < 10) { fprintf(stderr, "usage: see header\n"); return 1; }
    parse(argv[1]); string md = argv[2]; mode = md == "RWL";
    long long simT = atoll(argv[3]); bsz = max(1, atoi(argv[4])); bmaxT = atoll(argv[5]);
    if (mode == 0) { len1 = atoi(argv[6]); len2 = atoi(argv[7]); len3 = atoi(argv[8]); LRUn = atoi(argv[9]); }
    else { mnc = atoi(argv[6]); mod_ = max(1, atoi(argv[7])); len1 = atoi(argv[8]); len2 = atoi(argv[9]); }
    for (int i = 10; i < argc; i++) { string a = argv[i]; if (a == "-S") maxS = atoi(argv[++i]); else if (a == "-C") maxC = atoll(argv[++i]); }
    sym_of({});
    // ---- simulate the plain machine simT steps (DH semantics: the head faces the direction of its last move) ----
    long long W = 2 * simT + 16; vector<char> tape(W, 0); long long pos = simT + 8, lo = pos, hi = pos; int q = 0, dir = 1;
    for (long long t = 0; t < simT; t++) {
        Tr tr = T[q][(int)tape[pos]];
        if (tr.halt) { printf("HALT %lld\n", t); return 0; }
        tape[pos] = tr.w; pos += tr.d ? 1 : -1; dir = tr.d; q = tr.s; lo = min(lo, pos); hi = max(hi, pos);
    }
    // front side: pos, pos+dirstep, ... ; behind side: the other cells, nearest first
    int step = dir ? 1 : -1;
    vector<int> front, behind;
    for (long long p = pos; p >= lo && p <= hi; p += step) front.push_back(tape[p]);
    for (long long p = pos - step; p >= lo && p <= hi; p -= step) behind.push_back(tape[p]);
    for (int s = 0; s < 2; s++) { D[s].get_state({}); D[s].trans[0] = 0; D[s].preds[0].push_back({0, 0}); }
    auto load = [&](int side, vector<int> cells) {
        // inv_map_cside: blocks of bsz from the head outward, the last padded with 0 (cells list nearest first)
        vector<vector<int>> blocks;
        if (cells.empty()) blocks.push_back(vector<int>(bsz, 0));
        for (size_t i = 0; i < cells.size(); i += bsz) {
            vector<int> b; for (int j = 0; j < bsz; j++) b.push_back(i + j < cells.size() ? cells[i + j] : 0);
            blocks.push_back(b);
        }
        int x = 0;
        for (int i = blocks.size() - 1; i >= 0; i--) { int y = sym_of(blocks[i]); if (y < 0) return -1; x = trans_add(side, x, y); }
        return x;
    };
    int fs = load(dir, front), bs = load(1 - dir, behind);
    if (fs < 0 || bs < 0) { puts("LIMIT syms"); return 0; }
    add_cfg({fs, bs, q, dir});
    bool abshalt = false;
    while (!work.empty()) {
        auto [ci, p] = work.front(); work.pop_front();
        Cfg c = cfgs[ci]; int xp = p.first, y = p.second;
        BRes r;
        if (!block_step(c.s, c.sgn, y, r)) { if (overflow) break; abshalt = true; break; }
        if (r.d == c.sgn) add_cfg({xp, trans_add(1 - c.sgn, c.b, r.y), r.q, c.sgn});
        else add_cfg({c.b, trans_add(c.sgn, xp, r.y), r.q, r.d});
        if (overflow) break;
        if ((long long)cfgs.size() > maxC) { overflow = true; break; }
    }
    printf("%s %zu %zu %zu %zu\n", abshalt ? "UNKNOWN" : overflow ? "LIMIT" : "NONHALT", cfgs.size(), syms.size(), D[0].st.size(), D[1].st.size());
}
