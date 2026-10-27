/* driver for gx3.c (positions as forms over NV variables; here constants only) */
#define main engine_main
#include ENGINE
#undef main
#include "drv_common.h"
int main(int argc, char **argv) {
    int NR = argc > 1 ? atoi(argv[1]) : 8; static char line[1 << 16]; char t[256]; long long p[256], W; int n;
    static Coset C0; CO = &C0; nv = 1; X[0] = 1;
    while (fgets(line, sizeof line, stdin)) {
        if (!read_state(line, &W, t, p, &n)) { printf("bad input\n.\n"); continue; }
        if (n + 2 > MAXM) { printf("U\n.\n"); continue; }
        memset(&S, 0, sizeof S); S.W = fconst(W); NFORCED = 0; FI = 0; NEEDBR = 0;
        add('G', fconst(1));
        for (int i = 0; i < n; i++) add(t[i], fconst(p[i]));
        const char *end = "E";
        for (int r = 0; r < NR; r++) {
            do_round();
            if (S.halted) { end = "H"; break; }
            if (S.bad || NEEDBR || S.W.e) { end = "U"; break; }
            char sh[16]; int idx[MAXM], k; shape(&S, sh, idx, &k);
            if (k == 0 || S.T[idx[0]] != 'G' || !fisconst(S.P[idx[0]], 1)) { end = "U"; break; }
            printf("R %lld", (long long)S.W.c[NV]);
            for (int i = 1; i < k; i++) printf(" %c %lld", S.T[idx[i]], (long long)S.P[idx[i]].c[NV]);
            printf("\n");
        }
        printf("%s\n.\n", end); fflush(stdout);
    }
    return 0;
}
