// Fast simulator of the block-level law shared by three BB(6) holdouts (see README.md).
// usage: lsim K MAXSTEPS [stat | ends [WIDTH]]
//   K        the start: the return state on blank tape with K ones behind the head
//            (1: 1RB0RC_1LC1LA_1RD0LB_1RE1RC_1RA0RF_1RC---, 2: 1RB0RF_1RC0RD_1LD1LB_1RE0LC_1RA1RD_1RD---,
//             0: 1RB1RE_1LC0RA_1LD1LB_1LE0LF_1LA0LB_1LB---, whose tape is the mirror image)
//   stat     (default) a line at every power of 10 of the step count, then totals
//   ends     the gap list each time the head turns at the block end of the tape
// The rules are those of lean/Law.lean and py/law.py; the stacks are run-length coded and two rules are applied in
// bulk (a run of gaps 2 2 in state C, a run of blocks 5 on the way back), so the step count is exact.
// build: g++ -O2 -o /tmp/lsim holdouts/MACHINE/c/lsim.cpp
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <vector>
#include <string>
using namespace std;
typedef unsigned __int128 u128; typedef uint64_t u64;
const u64 INF = ~0ULL;
struct Run { u64 v, n; };
struct Stack {
    vector<Run> a;
    void push(u64 v, u64 n = 1) { if (!n) return; if (!a.empty() && a.back().v == v) a.back().n += n; else a.push_back({v, n}); }
    bool empty() const { return a.empty(); }
    u64 top() const { return a.back().v; }
    u64 topn() const { return a.back().n; }
    u64 pop() { u64 v = a.back().v; if (--a.back().n == 0) a.pop_back(); return v; }
    void popn(u64 n) { a.back().n -= n; if (a.back().n == 0) a.pop_back(); }
};
struct LM {
    Stack L, G; u64 o = 0, g = 0, z = 0; char q = 'B'; u128 steps = 0; u64 macro = 0; bool halted = false;
    u64 maxo = 0, maxb = 0, maxg = 0;
    u64 blockseen[64] = {0}, gapseen[64] = {0}; u64 fsteps = 0, minFgap = INF; u64 th[5][8] = {{0}};   // th[kind][min(gap,7)]: c_turn0, c_turn4, c_turn5, d_turn3, d_turn4 (7 = larger or blank)
    u64 popL() { return L.empty() ? 0 : L.pop(); }
    u64 popG() { return G.empty() ? INF : G.pop(); }
    void pushG(u64 g_, u64 n = 1) { if (g_ != INF) { G.push(g_, n); gapseen[g_ < 63 ? g_ : 63] += n; if (g_ > maxg) maxg = g_; } }
    void pushL(u64 b, u64 n = 1) { L.push(b, n); blockseen[b < 63 ? b : 63] += n; if (b > maxb) maxb = b; }
    void turn(u64 k) {
        q = 'B';
        if (g == k) { o += k + 1; z = popG(); th[k == 4 ? 1 : 3][z < 7 ? z : 7]++; }
        else { pushL(o + k); o = 0; z = (g == INF) ? INF : g - k - 1; th[k == 4 ? 2 : 4][z < 7 ? z : 7]++; }
    }
    void step() {
        macro++;
        if (o > maxo) maxo = o;
        if (q == 'B') {
            if (o >= 3) {
                u64 k = o / 3; o %= 3;
                pushG(z == INF ? INF : z + 1); z = 1; pushG(2, k - 1); steps += (u128)5 * k;
            } else if (o == 2) { u64 b = popL(); o = b + 3; q = 'D'; g = z; steps += 7; }
            else if (o == 1) {
                if (!L.empty() && L.top() == 5 && z == 1) {     // bulk: 5^n with o = 1, z = 1 -> 2^(2n)
                    u64 n = L.topn(); L.popn(n); pushG(2, 2 * n); steps += (u128)12 * n; return;
                }
                u64 b = popL();
                if (b >= 1) { o = b - 1; pushG(z == INF ? INF : z + 1); z = 1; steps += 7; }
                else { u64 b2 = popL(); o = b2 + 3; q = 'D'; g = z; steps += 9; }
            } else {
                u64 b = popL();
                if (b >= 1) { o = b - 1; pushG(z); z = 1; steps += 2; }
                else { u64 b2 = popL(); o = b2 + 2; q = 'C'; g = z; steps += 3; }
            }
            return;
        }
        if (q == 'C') {
            if (g == 0) { q = 'B'; u64 g2 = popG(); z = (g2 == INF) ? INF : 1 + g2; steps += 1; th[0][g2 < 7 ? g2 : 7]++; }
            else if (g == 1) { o += 2; g = popG(); steps += 2; }
            else if (g == 2) {
                // bulk: g = 2 followed by 2^m on G: pairs
                if (!G.empty() && G.top() == 2) {
                    u64 m = G.topn() + 1;            // number of 2s including current
                    u64 pairs = m / 2;
                    pushL(o + 2); pushL(5, pairs - 1); o = 3; steps += (u128)6 * pairs; fsteps += pairs; if (minFgap > 2) minFgap = 2;
                    G.popn(2 * pairs - 1); g = popG(); return;
                }
                pushL(o + 2); o = 0; q = 'F'; g = popG(); steps += 3;
            }
            else if (g == 3) { pushL(o + 3); o = 0; g = popG(); steps += 4; }
            else { turn(4); steps += 4; }
        } else if (q == 'F') {
            fsteps++; if (g < minFgap) minFgap = g;
            if (g == 0) { halted = true; return; }
            o += 1; g = (g == INF) ? INF : g - 1; q = 'C'; steps += 1;
        } else {  // D
            if (g == 0) { o += 1; q = 'C'; g = popG(); steps += 1; }
            else if (g == 1) { pushL(o + 1); o = 0; q = 'F'; g = popG(); steps += 2; }
            else if (g == 2) { pushL(o + 2); o = 0; q = 'C'; g = popG(); steps += 3; }
            else { turn(3); steps += 3; }
        }
    }
};
static string u128s(u128 x) { if (!x) return "0"; string s; while (x) { s = char('0' + (int)(x % 10)) + s; x /= 10; } return s; }
static void pr(u64 v) { if (v == INF) printf("inf"); else printf("%llu", (unsigned long long)v); }
int main(int argc, char** argv) {
    int K = atoi(argv[1]); double maxsteps = atof(argv[2]); string mode = argc > 3 ? argv[3] : "stat";
    int width = argc > 4 ? atoi(argv[4]) : 40;
    LM m;
    // start: 1^K B> 0^inf : B on a 0 with K ones to its left: closed block K, open 0, z = inf
    m.q = 'B'; m.o = 0; m.z = INF; if (K) m.L.push(K);
    m.steps = (K == 1) ? 1 : (K == 2) ? 2 : 0;
    u64 ends = 0; double next = 1e3;
    while (!m.halted && (double)m.steps < maxsteps) {
        char pq = m.q;
        m.step();
        if (pq == 'B' && m.q != 'B' && m.L.empty()) {
            ends++;
            if (mode == "ends") {
                printf("%s %c %llu | ", u128s(m.steps).c_str(), m.q, (unsigned long long)m.o); pr(m.g);
                int c = 0;
                for (auto it = m.G.a.rbegin(); it != m.G.a.rend() && c < width; ++it, ++c) { printf(" %llu", (unsigned long long)it->v); if (it->n > 1) printf("^%llu", (unsigned long long)it->n); }
                printf("\n");
            }
        }
        if (mode == "stat" && (double)m.steps >= next) {
            u64 cells = 0, runs = m.G.a.size() + m.L.a.size();
            for (auto& r : m.G.a) cells += (r.v + 1) * r.n;
            for (auto& r : m.L.a) cells += (r.v + 1) * r.n;
            printf("steps %s macro %llu leftends %llu runs %llu cells~%llu maxo %llu maxblock %llu maxgap %llu\n", u128s(m.steps).c_str(),
                   (unsigned long long)m.macro, (unsigned long long)ends, (unsigned long long)runs, (unsigned long long)cells,
                   (unsigned long long)m.maxo, (unsigned long long)m.maxb, (unsigned long long)m.maxg);
            fflush(stdout);
            next *= 10;
        }
    }
    if (m.halted) printf("HALT after %s steps (F reads 1; bbchallenge count %s)\n", u128s(m.steps).c_str(), u128s(m.steps + 1).c_str());
    printf("final steps %s macro %llu\nblocks closed:", u128s(m.steps).c_str(), (unsigned long long)m.macro);
    for (int i = 0; i < 64; i++) if (m.blockseen[i]) printf(" %d%s:%llu", i, i == 63 ? "+" : "", (unsigned long long)m.blockseen[i]);
    printf("\ngaps closed:");
    for (int i = 0; i < 64; i++) if (m.gapseen[i]) printf(" %d%s:%llu", i, i == 63 ? "+" : "", (unsigned long long)m.gapseen[i]);
    const char* tn[5] = {"c_turn0: next gap", "c_turn4: next gap", "c_turn5: rest of the gap", "d_turn3: next gap", "d_turn4: rest of the gap"};
    for (int k = 0; k < 5; k++) { printf("\n%s", tn[k]); for (int i = 0; i < 8; i++) if (m.th[k][i]) printf(" %d%s:%llu", i, i == 7 ? "+" : "", (unsigned long long)m.th[k][i]); }
    printf("\nstate F entered %llu times, smallest gap it met: ", (unsigned long long)m.fsteps); pr(m.minFgap);
    printf("\n");
}
