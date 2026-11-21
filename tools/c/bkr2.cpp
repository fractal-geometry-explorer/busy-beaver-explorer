// backward reasoning, BFS by depth with dedup of stencils (state + known cells relative to head)
extern "C" {
#include "tm.h"
}
#include <set>
#include <map>
#include <vector>
using namespace std;
typedef pair<int, map<int,int>> St;
int main(int c, char **v) {
    tm_machine M; tm_parse(v[1], &M); int D = atoi(v[2]); size_t cap = atoll(v[3]);
    set<St> cur;
    for (int q = 0; q < M.n; q++) for (int s = 0; s < 2; s++) if (M.s[q][s] < 0) cur.insert({q, {{0, s}}});
    for (int d = 0; d < D; d++) {
        set<St> nx;
        for (auto &st : cur) for (int p = 0; p < M.n; p++) for (int s = 0; s < 2; s++) {
            if (M.s[p][s] != st.first) continue;
            int w = M.w[p][s], hp = -M.d[p][s];
            auto it = st.second.find(hp);
            if (it != st.second.end() && it->second != w) continue;
            map<int,int> t; for (auto &kv : st.second) t[kv.first - hp] = kv.second; t[0] = s;
            nx.insert({p, t});
        }
        if (nx.empty()) { printf("DECIDED %d\n", d + 1); return 0; }
        if (nx.size() > cap) { printf("BUDGET depth %d size %zu\n", d, nx.size()); return 0; }
        cur.swap(nx);
    }
    printf("FAIL depth %d size %zu\n", D, cur.size()); return 0;
}
