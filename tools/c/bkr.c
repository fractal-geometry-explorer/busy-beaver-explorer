/* bkr.c: backward reasoning (as busycoq BackwardsReasoning.v): DFS from every halting stencil, depth <= D.
   Prints DECIDED d (every chain dies within d steps) or FAIL (a chain of length D exists) or BUDGET. */
#include "tm.h"
#define W 4096
static tm_machine M; static long long nodes, budget; static int D, maxd;
static signed char tape[2*W+1];
/* returns 1 if some chain reaches depth D */
static int dfs(int q, int h, int depth) {
    if (depth > maxd) maxd = depth;
    if (depth >= D) return 1;
    if (++nodes > budget) return 2;
    for (int p = 0; p < M.n; p++) for (int s = 0; s < 2; s++) {
        if (M.s[p][s] != q) continue;
        int w = M.w[p][s], d = M.d[p][s], hp = h - d;
        if (tape[hp] >= 0 && tape[hp] != w) continue;
        signed char old = tape[hp]; tape[hp] = s;
        int r = dfs(p, hp, depth + 1);
        tape[hp] = old;
        if (r) return r;
    }
    return 0;
}
int main(int c, char **v) {
    if (tm_parse(v[1], &M)) return 1;
    D = atoi(v[2]); budget = c > 3 ? atoll(v[3]) : 100000000LL; if (D >= W) D = W - 1;
    memset(tape, -1, sizeof tape);
    for (int q = 0; q < M.n; q++) for (int s = 0; s < 2; s++) if (M.s[q][s] < 0) {
        tape[W] = s; int r = dfs(q, W, 0); tape[W] = -1;
        if (r == 1) { printf("FAIL depth %d nodes %lld\n", D, nodes); return 0; }
        if (r == 2) { printf("BUDGET maxdepth %d nodes %lld\n", maxd, nodes); return 0; }
    }
    printf("DECIDED %d nodes %lld\n", maxd + 1, nodes); return 0;
}
