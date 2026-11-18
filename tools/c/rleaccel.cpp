// C++ port of tools/py/bbtools/rleaccel.py (same algorithm, same policy, so macro-step counts agree with the
// Python program run for run): run-length tape of K-cell blocks, chain steps, and cycle jumps used only after the
// one-cycle rule has been proved by a symbolic replay.  Counts are 64-bit (the program stops with OVERFLOW when a
// run length passes 2^61 or the step count passes 2^125), so it is for machines of polynomial growth.
//
// usage: rleaccel MACHINE K MAX_MACRO [checkpoint-file [seconds-between-checkpoints]]
//   prints lines "macro N steps S cells W"; with a checkpoint file the tape is saved there and a later call resumes
//   (rules are learned again after a resume, so macro counts then differ from an uninterrupted run; steps are exact).
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <ctime>
#include <string>
#include <vector>
#include <unordered_map>
using namespace std;
typedef int64_t i64;
typedef __int128 i128;
typedef unsigned __int128 u128;
static const i64 INF = -1;

struct Tr { int kind; int ns, nq, nd; i64 st; };   // kind 0 ok, 1 halt, 2 loop
static int T[8][2][3]; static bool Thalt[8][2];
static int K, NST;
static Tr memo[8][64][2]; static bool have[8][64][2];

static void parse(const char *m) {
    int q = 0; const char *p = m;
    while (*p) {
        for (int b = 0; b < 2; b++) {
            if (p[0] == '-') Thalt[q][b] = true;
            else { Thalt[q][b] = false; T[q][b][0] = p[0] - '0'; T[q][b][1] = p[1] == 'R' ? 1 : -1; T[q][b][2] = p[2] - 'A'; }
            p += 3;
        }
        q++; if (*p == '_') p++;
    }
    NST = q;
}
static Tr &trans(int q, int sym, int d) {
    int di = d == 1 ? 1 : 0;
    if (have[q][sym][di]) return memo[q][sym][di];
    int cells[8]; for (int i = 0; i < K; i++) cells[i] = (sym >> (K - 1 - i)) & 1;
    int pos = d == 1 ? 0 : K - 1; i64 steps = 0; Tr r; int q0 = q;
    vector<vector<int>> seen;
    while (true) {
        vector<int> st; st.push_back(q); st.push_back(pos); for (int i = 0; i < K; i++) st.push_back(cells[i]);
        bool dup = false; for (auto &s : seen) if (s == st) { dup = true; break; }
        if (dup) { r.kind = 2; break; }
        seen.push_back(st);
        int c = cells[pos];
        if (Thalt[q][c]) { r.kind = 1; r.st = steps + 1; break; }
        cells[pos] = T[q][c][0]; pos += T[q][c][1]; q = T[q][c][2]; steps++;
        if (pos < 0 || pos >= K) {
            int ns = 0; for (int i = 0; i < K; i++) ns = ns * 2 + cells[i];
            r.kind = 0; r.ns = ns; r.nq = q; r.nd = pos >= K ? 1 : -1; r.st = steps; break;
        }
    }
    have[q0][sym][di] = true; memo[q0][sym][di] = r; return memo[q0][sym][di];
}

struct Run { int sym; i64 cnt; };
struct Key {
    uint64_t a, b, c;
    bool operator==(const Key &o) const { return a == o.a && b == o.b && c == o.c; }
};
struct KeyHash { size_t operator()(const Key &k) const { uint64_t h = k.a * 0x9E3779B97F4A7C15ULL; h ^= (k.b + 0x7F4A7C15ULL) * 0xC2B2AE3D27D4EB4FULL; h ^= (k.c + 13) * 0x165667B19E3779F9ULL; return h ^ (h >> 29); } };

static const int W = 8;
struct Lin { i64 c; vector<pair<int, i64>> a; };
static Lin lin_add(const Lin &x, const Lin &y, i64 mul) {
    Lin r; r.c = x.c + y.c * mul; r.a = x.a;
    for (auto &p : y.a) {
        bool f = false;
        for (size_t i = 0; i < r.a.size(); i++) if (r.a[i].first == p.first) {
            r.a[i].second += p.second * mul; f = true;
            if (r.a[i].second == 0) r.a.erase(r.a.begin() + i);
            break;
        }
        if (!f && p.second * mul != 0) r.a.push_back(make_pair(p.first, p.second * mul));
    }
    return r;
}
struct SRun { int sym; bool islin; i64 cnt; Lin lin; };
struct Rule {
    vector<int> spec[2]; vector<i64> consts[2]; vector<i64> mins, deltas; i128 sc; vector<i128> sa; vector<pair<int, int>> home;
};
struct Past { int q, d; vector<Run> L, R; uint64_t nmacro; uint64_t prevdelta; };

static vector<Run> L, R; static int q = 0, d = 1;
static u128 steps = 0; static uint64_t nmacro = 0;
static int halted = 0; static const char *nonhalt = 0; static bool overflow_ = false;
static unordered_map<Key, Past, KeyHash> past;
static unordered_map<Key, vector<Rule>, KeyHash> rules;
static unordered_map<Key, int, KeyHash> fails;
static uint64_t nrules = 0, njumps = 0, nproofs = 0, proofcost = 0;
static const uint64_t maxloop = 4000; static const i64 gen_thresh = 4;

static Key sig() {
    Key k; k.a = 0; k.b = 0;
    size_t nl = L.size() < (size_t)W ? L.size() : W, nr = R.size() < (size_t)W ? R.size() : W;
    for (size_t i = L.size() - nl; i < L.size(); i++) k.a = k.a * 64 + L[i].sym;
    for (size_t i = R.size() - nr; i < R.size(); i++) k.b = k.b * 64 + R[i].sym;
    k.c = (uint64_t)q | ((uint64_t)(d == 1) << 4) | ((uint64_t)nl << 8) | ((uint64_t)nr << 16);
    return k;
}
static inline void basic() {
    vector<Run> &stack = d == 1 ? R : L, &other = d == 1 ? L : R;
    Run &top = stack.back();
    int sym = top.sym; i64 cnt = top.cnt;
    Tr &tr = trans(q, sym, d);
    if (tr.kind != 0) {
        if (tr.kind == 1) { steps += tr.st; halted = 1; } else nonhalt = "in-block loop";
        return;
    }
    if (tr.nq == q && tr.nd == d) {
        if (cnt == INF) { nonhalt = "runs off to infinity"; return; }
        stack.pop_back();
        steps += (u128)cnt * (u128)tr.st;
        Run &o = other.back();
        if (o.sym == tr.ns) { if (o.cnt != INF) { o.cnt += cnt; if (o.cnt > ((i64)1 << 61)) overflow_ = true; } }
        else other.push_back(Run{tr.ns, cnt});
        return;
    }
    if (cnt != INF) { if (cnt == 1) stack.pop_back(); else top.cnt = cnt - 1; }
    vector<Run> &tgt = tr.nd == d ? other : stack;
    Run &o = tgt.back();
    if (o.sym == tr.ns) { if (o.cnt != INF) o.cnt += 1; }
    else tgt.push_back(Run{tr.ns, 1});
    q = tr.nq; d = tr.nd; steps += tr.st;
}

struct ProofFail {};
static void spush(vector<SRun> &st, int ns, const SRun &c) {
    if (!st.empty() && st.back().sym == ns) {
        SRun &o = st.back();
        if (!o.islin && o.cnt == INF) return;
        if (!o.islin && !c.islin) o.cnt += c.cnt;
        else if (!o.islin) { Lin t; t.c = o.cnt; o.lin = lin_add(c.lin, t, 1); o.islin = true; }
        else if (!c.islin) o.lin.c += c.cnt;
        else o.lin = lin_add(o.lin, c.lin, 1);
    } else { SRun n = c; n.sym = ns; st.push_back(n); }
}
static Rule try_prove(const Past &old, uint64_t nloops) {
    nproofs++;
    vector<SRun> SL, SR; vector<i64> mins; vector<pair<int, int>> home; int nv = 0;
    size_t nl = L.size() < (size_t)W ? L.size() : W, nr = R.size() < (size_t)W ? R.size() : W;
    for (int side = 0; side < 2; side++) {
        const vector<Run> &src = side == 0 ? old.L : old.R; const vector<Run> &cur = side == 0 ? L : R;
        size_t off = side == 0 ? L.size() - nl : R.size() - nr;
        vector<SRun> &dst = side == 0 ? SL : SR;
        for (size_t i = 0; i < src.size(); i++) {
            i64 c = src[i].cnt; SRun s; s.sym = src[i].sym;
            if (c != INF && (c != cur[off + i].cnt || c >= gen_thresh)) {
                s.islin = true; s.cnt = 0; s.lin.c = 0; s.lin.a.push_back(make_pair(nv, (i64)1));
                mins.push_back(1); home.push_back(make_pair(side, (int)i)); nv++;
            } else { s.islin = false; s.cnt = c; }
            dst.push_back(s);
        }
    }
    int pq = old.q, pd = old.d; Lin stp; stp.c = 0; i128 stc = 0; vector<i128> sta(nv, 0);
    for (uint64_t it = 0; it < nloops; it++) {
        vector<SRun> &stack = pd == 1 ? SR : SL, &other = pd == 1 ? SL : SR;
        if (stack.empty()) throw ProofFail();
        SRun top = stack.back();
        Tr &tr = trans(pq, top.sym, pd);
        if (tr.kind != 0) throw ProofFail();
        if (tr.nq == pq && tr.nd == pd) {
            if (!top.islin && top.cnt == INF) throw ProofFail();
            stack.pop_back();
            if (!top.islin) stc += (i128)top.cnt * tr.st;
            else { stc += (i128)top.lin.c * tr.st; for (auto &p : top.lin.a) sta[p.first] += (i128)p.second * tr.st; }
            spush(other, tr.ns, top);
            continue;
        }
        if (!(!top.islin && top.cnt == INF)) {
            if (!top.islin) { if (top.cnt == 1) stack.pop_back(); else stack.back().cnt = top.cnt - 1; }
            else {
                // need count >= 2 under the current minimums
                Lin &e = stack.back().lin; i64 lo = e.c;
                for (auto &p : e.a) { if (p.second < 0) throw ProofFail(); lo += p.second * mins[p.first]; }
                if (lo < 2) {
                    if (e.a.size() == 1 && e.a[0].second == 1) mins[e.a[0].first] = 2 - e.c;
                    else throw ProofFail();
                }
                e.c -= 1;
            }
        }
        SRun one; one.islin = false; one.cnt = 1; one.sym = tr.ns;
        spush(tr.nd == pd ? other : stack, tr.ns, one);
        pq = tr.nq; pd = tr.nd; stc += tr.st;
    }
    if (pq != old.q || pd != old.d || SL.size() != old.L.size() || SR.size() != old.R.size()) throw ProofFail();
    Rule r; r.deltas.assign(nv, 0); int vi = 0;
    for (int side = 0; side < 2; side++) {
        vector<SRun> &fin = side == 0 ? SL : SR; const vector<Run> &src = side == 0 ? old.L : old.R;
        for (size_t i = 0; i < fin.size(); i++) {
            if (fin[i].sym != src[i].sym) throw ProofFail();
            if (vi < nv && home[vi].first == side && home[vi].second == (int)i) {
                if (!fin[i].islin || fin[i].lin.a.size() != 1 || fin[i].lin.a[0].first != vi || fin[i].lin.a[0].second != 1) throw ProofFail();
                r.deltas[vi] = fin[i].lin.c; r.spec[side].push_back(vi); vi++;
            } else {
                if (fin[i].islin || fin[i].cnt != src[i].cnt) throw ProofFail();
                r.spec[side].push_back(-1);
            }
            r.consts[side].push_back(src[i].cnt);
        }
    }
    r.mins = mins; r.sc = stc; r.sa = sta; r.home = home;
    return r;
}
static bool apply_rule(const Rule &r) {
    size_t nl = L.size() < (size_t)W ? L.size() : W, nr = R.size() < (size_t)W ? R.size() : W;
    size_t offs[2] = {L.size() - nl, R.size() - nr};
    i64 xs[2 * W + 2]; int nx = 0;
    for (int side = 0; side < 2; side++) {
        vector<Run> &cur = side == 0 ? L : R; size_t n = side == 0 ? nl : nr;
        if (r.spec[side].size() != n) return false;
        for (size_t i = 0; i < n; i++) {
            i64 c = cur[offs[side] + i].cnt; int v = r.spec[side][i];
            if (v < 0) { if (c != r.consts[side][i]) return false; }
            else { if (c == INF || c < r.mins[v]) return false; xs[nx++] = c; }
        }
    }
    i64 k = -1;
    for (size_t v = 0; v < r.deltas.size(); v++) if (r.deltas[v] < 0) {
        i64 kk = (xs[v] - r.mins[v]) / (-r.deltas[v]) + 1;
        if (k < 0 || kk < k) k = kk;
    }
    if (k < 0) { nonhalt = "cycle rule repeats forever"; return true; }
    i128 st = (i128)k * r.sc;
    for (size_t v = 0; v < r.deltas.size(); v++) {
        int side = r.home[v].first, i = r.home[v].second;
        i128 nv = (i128)xs[v] + (i128)k * r.deltas[v];
        if (nv > ((i128)1 << 61)) overflow_ = true;
        (side == 0 ? L : R)[offs[side] + i].cnt = (i64)nv;
        st += r.sa[v] * ((i128)k * xs[v] + (i128)r.deltas[v] * (((i128)k * (k - 1)) / 2));
    }
    steps += (u128)st; njumps++;
    return true;
}
static void run(uint64_t max_macro) {
    while (nmacro < max_macro && !halted && !nonhalt && !overflow_) {
        nmacro++;
        Key s = sig();
        auto ri = rules.find(s);
        bool done = false;
        if (ri != rules.end()) for (auto &r : ri->second) if (apply_rule(r)) { done = true; break; }
        if (done) { past.clear(); continue; }
        auto pi = past.find(s);
        bool hadold = pi != past.end(); uint64_t oldn = hadold ? pi->second.nmacro : 0;
        if (hadold) {
            uint64_t nl = nmacro - pi->second.nmacro;
            auto fi = fails.find(s);
            if (nl == pi->second.prevdelta && nl <= maxloop && (fi == fails.end() || fi->second < 3) && proofcost <= 2 * nmacro + 100000) {
                proofcost += nl;
                try {
                    Rule r = try_prove(pi->second, nl);
                    vector<Rule> &v = rules[s]; v.push_back(r); nrules++;
                    if (apply_rule(v.back())) { past.clear(); continue; }
                } catch (ProofFail &) { fails[s]++; }
            }
        }
        Past p; p.q = q; p.d = d;
        size_t nl = L.size() < (size_t)W ? L.size() : W, nr = R.size() < (size_t)W ? R.size() : W;
        p.L.assign(L.end() - nl, L.end()); p.R.assign(R.end() - nr, R.end());
        p.nmacro = nmacro; p.prevdelta = hadold ? nmacro - oldn : 0;
        past[s] = p;
        if (past.size() > 20000) past.clear();
        if (rules.size() > 200000) { rules.clear(); fails.clear(); }
        basic();
        if (steps > ((u128)1 << 125)) overflow_ = true;
    }
}
static string dec(u128 x) { if (x == 0) return "0"; string s; while (x) { s = char('0' + (int)(x % 10)) + s; x /= 10; } return s; }
static u128 width() { u128 w = 0; for (size_t i = 1; i < L.size(); i++) w += L[i].cnt; for (size_t i = 1; i < R.size(); i++) w += R[i].cnt; return w * K; }
static void save(const char *fn) {
    string tmp = string(fn) + ".tmp"; FILE *f = fopen(tmp.c_str(), "wb"); if (!f) return;
    uint64_t nL = L.size(), nR = R.size(); int32_t qq = q, dd = d;
    fwrite(&nmacro, 8, 1, f); fwrite(&steps, 16, 1, f); fwrite(&qq, 4, 1, f); fwrite(&dd, 4, 1, f); fwrite(&nL, 8, 1, f); fwrite(&nR, 8, 1, f);
    fwrite(L.data(), sizeof(Run), nL, f); fwrite(R.data(), sizeof(Run), nR, f); fclose(f); rename(tmp.c_str(), fn);
}
static bool load(const char *fn) {
    FILE *f = fopen(fn, "rb"); if (!f) return false;
    uint64_t nL, nR; int32_t qq, dd;
    if (fread(&nmacro, 8, 1, f) != 1) { fclose(f); return false; }
    if (fread(&steps, 16, 1, f) != 1 || fread(&qq, 4, 1, f) != 1 || fread(&dd, 4, 1, f) != 1 || fread(&nL, 8, 1, f) != 1 || fread(&nR, 8, 1, f) != 1) { fclose(f); return false; }
    L.resize(nL); R.resize(nR);
    if (fread(L.data(), sizeof(Run), nL, f) != nL || fread(R.data(), sizeof(Run), nR, f) != nR) { fclose(f); return false; }
    fclose(f); q = qq; d = dd; return true;
}
int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: rleaccel MACHINE K MAX_MACRO [checkpoint [seconds]]\n"); return 2; }
    parse(argv[1]); K = atoi(argv[2]);
    if (K < 1 || K > 6) { fprintf(stderr, "K must be 1..6 (the transition memo is sized for 64 block symbols)\n"); return 2; } uint64_t mx = strtoull(argv[3], 0, 10);
    const char *ck = argc > 4 ? argv[4] : 0; long every = argc > 5 ? atol(argv[5]) : 900;
    L.push_back(Run{0, INF}); R.push_back(Run{0, INF});
    if (ck) load(ck);
    time_t last = time(0);
    while (nmacro < mx && !halted && !nonhalt && !overflow_) {
        uint64_t nxt = nmacro + 5000000; if (nxt > mx) nxt = mx;
        run(nxt);
        if (ck && (time(0) - last >= every || halted || nonhalt || overflow_ || nmacro >= mx)) {
            last = time(0); save(ck);
            printf("macro %llu steps %s cells %s\n", (unsigned long long)nmacro, dec(steps).c_str(), dec(width()).c_str()); fflush(stdout);
        }
    }
    printf("macro %llu steps %s cells %s rules %llu jumps %llu\n", (unsigned long long)nmacro, dec(steps).c_str(), dec(width()).c_str(), (unsigned long long)nrules, (unsigned long long)njumps);
    if (halted) printf("HALTED after %s steps\n", dec(steps).c_str());
    else if (nonhalt) printf("DOES NOT HALT: %s\n", nonhalt);
    else if (overflow_) printf("OVERFLOW (counts too large for this program)\n");
    else printf("no halt in the first %s steps\n", dec(steps).c_str());
    return 0;
}
