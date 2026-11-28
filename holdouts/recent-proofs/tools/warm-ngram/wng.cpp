// wng.cpp: a re-implementation of busycoq's CTL_NG_QSym decider (verify/CTL.v, module NGramCPS inside the CTL
// framework, with the QSym tape-history augmentation), plus the warm start of busycoq PR #121: the history machine
// is run for simT steps from blank tape and the closure starts from the configuration reached, histories included.
//
//   wng MACHINE simT NG_n len1 len2 LRU_n [-c] [-S maxS] [-C maxConfigs] [-d SYMFILE]
//
//   -d   write every tape symbol of the closure (bit, then its history newest first) to SYMFILE
//
//   -c   "cold" history: run the plain machine simT steps and start with every history empty (what busycoq's NG
//        decider does for simT > 0); default is the warm start of PR #121.
// Output: one line "RESULT configs syms lstates rstates" with RESULT in NONHALT / UNKNOWN (abstract halt) /
// LIMIT (maxS symbols or maxConfigs exceeded) / HALT (the machine halted within simT steps).
#include <bits/stdc++.h>
using namespace std;

struct Tr { int w, d, s; bool halt; };   // d: 0 = L, 1 = R
static Tr T[8][2];
static int NS;

static void parse(const string &m) {
    NS = 0;
    vector<string> rows; string cur;
    for (char c : m) { if (c == '_') { rows.push_back(cur); cur.clear(); } else cur += c; }
    rows.push_back(cur); NS = rows.size();
    for (int q = 0; q < NS; q++) for (int b = 0; b < 2; b++) {
        string t = rows[q].substr(3 * b, 3);
        if (t[2] < 'A' || t[2] > 'Z') { T[q][b] = {0, 0, 0, true}; continue; }
        T[q][b] = {t[0] - '0', t[1] == 'R', t[2] - 'A', false};
    }
}

// ---- symbols: (bit, history of (state,bit) pairs, newest first) ----
typedef vector<int> Hist;   // each entry = state*2+bit
struct Sym { int bit; Hist h; bool operator==(const Sym &o) const { return bit == o.bit && h == o.h; } };
struct SymH { size_t operator()(const Sym &s) const { size_t x = s.bit * 1000003u; for (int v : s.h) x = x * 131 + v + 7; return x; } };
static vector<Sym> syms;
static unordered_map<Sym, int, SymH> symid;
static int maxS = 30000;
static bool overflow = false;
static int sym_of(const Sym &s) {
    auto it = symid.find(s); if (it != symid.end()) return it->second;
    if ((int)syms.size() >= maxS) { overflow = true; return -1; }
    int id = syms.size(); syms.push_back(s); symid[s] = id; return id;
}
static int len1, len2, LRUn;
static Hist upd(int q, int bit, const Hist &h) {
    Hist l; l.reserve(h.size() + 1); l.push_back(q * 2 + bit); l.insert(l.end(), h.begin(), h.end());
    if ((int)l.size() <= len1) return l;           // upd_skipn on a short list: unchanged
    Hist out(l.begin(), l.begin() + len1);
    // upd_LRU len2 LRU_n on the remainder
    vector<int> rest(l.begin() + len1, l.end());
    int hd = rest[0];
    vector<int> t; int n = LRUn; bool removed = false;
    for (size_t i = 1; i < rest.size(); i++) {
        if (!removed && rest[i] == hd) { if (n == 0) { removed = true; continue; } n--; }
        t.push_back(rest[i]);
    }
    vector<int> r2; r2.push_back(hd); r2.insert(r2.end(), t.begin(), t.end());
    if ((int)r2.size() > len2) r2.resize(len2);
    out.insert(out.end(), r2.begin(), r2.end());
    return out;
}

// ---- n-gram DFAs, one per side ----
static int NGn;
struct VH { size_t operator()(const vector<int> &v) const { size_t x = 1469598103u; for (int a : v) x = x * 1000003u + a + 1; return x; } };
struct DFA {
    vector<vector<int>> st; unordered_map<vector<int>, int, VH> sid;
    unordered_map<long long, int> trans;          // (state<<20 | sym) -> state
    vector<vector<pair<int,int>>> preds;          // state -> (prev state, sym)
    vector<vector<int>> idx;                      // state -> configs with this front state on this side
    int get_state(const vector<int> &v) {
        auto it = sid.find(v); if (it != sid.end()) return it->second;
        int id = st.size(); st.push_back(v); sid[v] = id; preds.emplace_back(); idx.emplace_back(); return id;
    }
};
static DFA D[2];  // 0 = left, 1 = right
struct Cfg { int f, b, s, sgn; };
static vector<Cfg> cfgs;
static unordered_map<long long, int> cfgid;
static deque<pair<int, pair<int,int>>> work;     // (config, (pred state, sym))
static long long maxC = 20000000;
static bool abshalt = false;

static long long ck(const Cfg &c) { return (((long long)c.f * 4000000LL + c.b) * 8 + c.s) * 2 + c.sgn; }
static void add_cfg(const Cfg &c) {
    long long k = ck(c);
    if (cfgid.count(k)) return;
    int id = cfgs.size(); cfgs.push_back(c); cfgid[k] = id;
    DFA &F = D[c.sgn];
    F.idx[c.f].push_back(id);
    for (auto &p : F.preds[c.f]) work.push_back({id, p});
}
// returns trans(x,y) in DFA side, adding it (and waking waiting configs) if new
static int trans_add(int side, int x, int y) {
    DFA &A = D[side];
    long long key = ((long long)x << 20) | y;
    auto it = A.trans.find(key); if (it != A.trans.end()) return it->second;
    vector<int> v; v.push_back(y); for (int a : A.st[x]) { if ((int)v.size() >= NGn) break; v.push_back(a); }
    int z = A.get_state(v);
    A.trans[key] = z;
    A.preds[z].push_back({x, y});
    for (int c : A.idx[z]) if (cfgs[c].sgn == side) work.push_back({c, {x, y}});
    return z;
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: wng MACHINE simT NG_n len1 len2 LRU_n [-c] [-S maxS] [-C maxC]\n"); return 1; }
    parse(argv[1]);
    long long simT = atoll(argv[2]); NGn = atoi(argv[3]); len1 = atoi(argv[4]); len2 = atoi(argv[5]); LRUn = atoi(argv[6]);
    bool cold = false; const char *dump = nullptr;
    for (int i = 7; i < argc; i++) {
        string a = argv[i];
        if (a == "-c") cold = true;
        else if (a == "-S") maxS = atoi(argv[++i]);
        else if (a == "-C") maxC = atoll(argv[++i]);
        else if (a == "-d") dump = argv[++i];
    }
    sym_of({0, {}});   // s0 = id 0
    // ---- simulate ----
    long long W = 2 * simT + 16;
    vector<Sym> tape(W, Sym{0, {}});
    long long pos = simT + 8; int q = 0; int lastdir = 1;
    for (long long t = 0; t < simT; t++) {
        Sym &c = tape[pos];
        Tr tr = T[q][c.bit];
        if (tr.halt) { printf("HALT %lld\n", t); return 0; }
        Hist nh = cold ? Hist() : upd(q, c.bit, c.h);
        c.bit = tr.w; c.h = nh;
        pos += tr.d ? 1 : -1; lastdir = tr.d; q = tr.s;
    }
    // DH config: the head faces direction lastdir; the cell under the head is on the front side.
    for (int s = 0; s < 2; s++) { D[s].get_state({}); D[s].trans[(0LL << 20) | 0] = 0; D[s].preds[0].push_back({0, 0}); }
    // left side: cells pos-1, pos-2, ... ; right side: pos+1, ...; head cell goes to the front side (lastdir)
    long long lo = 0, hi = W - 1;
    while (lo < pos && tape[lo].bit == 0 && tape[lo].h.empty()) lo++;
    while (hi > pos && tape[hi].bit == 0 && tape[hi].h.empty()) hi--;
    int Ls = 0, Rs = 0;
    long long lend = lastdir == 0 ? pos : pos - 1;      // left side includes head cell if facing left
    long long rbeg = lastdir == 1 ? pos : pos + 1;
    for (long long i = lo; i <= lend; i++) { int y = sym_of(tape[i]); if (y < 0) { puts("LIMIT syms"); return 0; } Ls = trans_add(0, Ls, y); }
    for (long long i = hi; i >= rbeg; i--) { int y = sym_of(tape[i]); if (y < 0) { puts("LIMIT syms"); return 0; } Rs = trans_add(1, Rs, y); }
    Cfg c0 = lastdir == 1 ? Cfg{Rs, Ls, q, 1} : Cfg{Ls, Rs, q, 0};
    add_cfg(c0);
    // ---- closure ----
    while (!work.empty()) {
        auto [ci, p] = work.front(); work.pop_front();
        Cfg c = cfgs[ci];
        int xp = p.first, y = p.second;
        const Sym ys = syms[y];
        Tr tr = T[c.s][ys.bit];
        if (tr.halt) { abshalt = true; break; }
        Sym w{tr.w, upd(c.s, ys.bit, ys.h)};
        int yw = sym_of(w); if (yw < 0) break;
        if (tr.d == c.sgn) {
            int nb = trans_add(1 - c.sgn, c.b, yw);
            add_cfg({xp, nb, tr.s, c.sgn});
        } else {
            int nf = trans_add(c.sgn, xp, yw);
            add_cfg({c.b, nf, tr.s, tr.d});
        }
        if ((long long)cfgs.size() > maxC) { overflow = true; break; }
    }
    if (dump) { FILE *f = fopen(dump, "w"); for (auto &y : syms) { fprintf(f, "%d", y.bit); for (int v : y.h) fprintf(f, " %c%d", 'A' + v / 2, v % 2); fprintf(f, "\n"); } fclose(f); }
    const char *r = abshalt ? "UNKNOWN" : overflow ? "LIMIT" : "NONHALT";
    printf("%s %zu %zu %zu %zu\n", r, cfgs.size(), syms.size(), D[0].st.size(), D[1].st.size());
    return 0;
}
