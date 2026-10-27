/* driver for the route-tree engines with positions (a m + b E + c) / 2^e (rtree3d.c, rtree3e.c) */
#define main engine_main
#include ENGINE
#undef main
#include "drv_common.h"
int main(int argc, char **argv) {
    int NR = argc > 1 ? atoi(argv[1]) : 8; static char line[1 << 16]; char t[256]; long long p[256], W; int n;
    static Coset C0; CC = &C0;
    while (fgets(line, sizeof line, stdin)) {
        if (!read_state(line, &W, t, p, &n)) { printf("bad input\n.\n"); continue; }
        memset(&S, 0, sizeof S); S.W = fconst(W); NFRC = 0; FI = 0; BRANCH = 0; cerr = 0; OVF = 0;
        addm('G', fconst(1));
        for (int i = 0; i < n; i++) addm(t[i], fconst(p[i]));
        const char *end = "E";
        for (int r = 0; r < NR; r++) {
            do_round();
            if (S.halted) { end = "H"; break; }
            if (S.bad || BRANCH || cerr || OVF || S.W.e) { end = "U"; break; }
            sortmarks();
            if (nord == 0 || S.T[order[0]] != 'G' || fcmpk(S.P[order[0]], 1) != 0) { end = "U"; break; }
            printf("R %lld", S.W.c);
            for (int i = 1; i < nord; i++) printf(" %c %lld", S.T[order[i]], S.P[order[i]].c);
            printf("\n");
        }
        printf("%s\n.\n", end); fflush(stdout);
    }
    return 0;
}
