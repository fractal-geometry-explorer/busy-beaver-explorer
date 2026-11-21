// repwl.cpp: Repeated Word List decider (after Coq-BB5's RepWL), for two-symbol machines from blank tape.
// Abstract tape: head between blocks of LEN cells; each side a stack of (word, count), count 1..T-1 exact or T meaning ">= T".
// repwl MACHINE LEN T [MAXCONF]   -> NONHALT n | UNKNOWN (halt reachable) | LIMIT
extern "C" {
#include "tm.h"
}
#include <vector>
#include <string>
#include <unordered_set>
#include <unordered_map>
#include <deque>
using namespace std;
static tm_machine M; static int LEN, T;
typedef unsigned long long u64;
struct Res { int kind; int q; u64 w; }; // kind 0: exit right, 1: exit left, 2: halt, 3: loops forever
struct PH { size_t operator()(const pair<u64,int>&p) const { return p.first*1000003ULL ^ p.second; } };
static unordered_map<pair<u64,int>, Res, PH> memo2;
static long long CAP = 100000;
static Res block(int q, u64 w, int fromLeft) {
    pair<u64,int> key{w, (q << 1) | fromLeft};
    auto it = memo2.find(key); if (it != memo2.end()) return it->second;
    int pos = fromLeft ? 0 : LEN - 1; long long lim = LEN <= 16 ? (long long)M.n * LEN * (1LL << LEN) + 5 : CAP, k = 0;
    Res r;
    while (1) {
        if (pos < 0) { r = {1, q, w}; break; }
        if (pos >= LEN) { r = {0, q, w}; break; }
        if (++k > lim) { r = {LEN <= 16 ? 3 : 4, 0, 0}; break; }
        int y = (w >> pos) & 1, s = M.s[q][y];
        if (s < 0) { r = {2, 0, 0}; break; }
        if (M.w[q][y]) w |= 1ULL << pos; else w &= ~(1ULL << pos);
        pos += M.d[q][y]; q = s;
    }
    memo2[key] = r; return r;
}
typedef vector<pair<u64,int>> Side; // back = nearest the head
struct Cfg { int q, dir; Side L, R; }; // dir 1: head faces right (next block popped from R)
static string ser(const Cfg &c) {
    string s; s.push_back((char)c.q); s.push_back((char)c.dir);
    for (auto &p : c.L) { s.append((const char*)&p.first, 8); s.push_back((char)p.second); }
    s.push_back((char)255);
    for (auto &p : c.R) { s.append((const char*)&p.first, 8); s.push_back((char)p.second); }
    return s;
}
static void push(Side &s, u64 w) {
    if (s.empty() && w == 0) return;
    if (!s.empty() && s.back().first == w) { if (s.back().second < T) s.back().second++; return; }
    s.push_back({w, 1});
}
int main(int argc, char **argv) {
    if (argc < 4 || tm_parse(argv[1], &M)) { fprintf(stderr, "usage: repwl MACHINE LEN T [MAXCONF]\n"); return 1; }
    LEN = atoi(argv[2]); T = atoi(argv[3]); long long maxc = argc > 4 ? atoll(argv[4]) : 2000000; if (argc > 5) CAP = atoll(argv[5]); if (LEN > 62) return 1;
    unordered_set<string> seen; deque<Cfg> work;
    Cfg c0{0, 1, {}, {}}; seen.insert(ser(c0)); work.push_back(c0);
    while (!work.empty()) {
        Cfg c = work.front(); work.pop_front();
        Side &src = c.dir ? c.R : c.L;
        vector<pair<u64, Side>> pops; // (word, remaining side)
        if (src.empty()) pops.push_back({0ULL, src});
        else {
            auto top = src.back(); Side rest = src; rest.pop_back();
            if (top.second == 1) pops.push_back({top.first, rest});
            else if (top.second < T) { Side r2 = rest; r2.push_back({top.first, top.second - 1}); pops.push_back({top.first, r2}); }
            else { Side a = rest; a.push_back({top.first, T}); pops.push_back({top.first, a});
                   if (T - 1 >= 1) { Side b = rest; b.push_back({top.first, T - 1}); pops.push_back({top.first, b}); } }
        }
        for (auto &pp : pops) {
            Res r = block(c.q, pp.first, c.dir);
            if (r.kind == 4) { printf("UNKNOWN block_cap configs %zu\n", seen.size()); return 0; }
            if (r.kind == 2) { printf("UNKNOWN configs %zu\n", seen.size()); return 0; }
            if (r.kind == 3) continue;
            Cfg n; n.q = r.q;
            if (c.dir) { n.R = pp.second; n.L = c.L; } else { n.L = pp.second; n.R = c.R; }
            if (r.kind == 0) { push(n.L, r.w); n.dir = 1; } else { push(n.R, r.w); n.dir = 0; }
            if (n.L.size() > 400 || n.R.size() > 400) { printf("LIMIT long_list configs %zu\n", seen.size()); return 0; }
            string k = ser(n);
            if (seen.insert(k).second) { work.push_back(n); if ((long long)seen.size() > maxc) { printf("LIMIT configs %zu\n", seen.size()); return 0; } }
        }
    }
    printf("NONHALT configs %zu\n", seen.size()); return 0;
}
