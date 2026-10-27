/* driver for the list engines with positions a·j + b (nrefdfs2.c, lined.c): compile with -DENGINE='"file.c"' */
#define main engine_main
#include ENGINE
#undef main
#include "drv_common.h"
int main(int argc, char **argv) {
    int NR = argc > 1 ? atoi(argv[1]) : 8; static char line[1 << 16]; char t[256]; long long p[256], W; int n;
    while (fgets(line, sizeof line, stdin)) {
        if (!read_state(line, &W, t, p, &n)) { printf("bad input\n.\n"); continue; }
        CK = 0; CRHO = 0; NTHR = 0; PJ = 0; PROBE_N = 0;
        memset(&S, 0, offsetof(St, T)); S.head = S.tail = -1; S.W = (Q){0, W}; S.alld = 7; NDL[0] = NDL[1] = NDL[2] = 0;
        addm_after('G', (Q){0, 1}, -1);
        for (int i = 0; i < n; i++) addm_after(t[i], (Q){0, p[i]}, S.tail);
        const char *end = "E";
        for (int r = 0; r < NR; r++) {
            do_round();
            if (S.halted) { end = "H"; break; }
            if (S.bad || S.need) { end = "U"; break; }
            int h = S.head; if (h < 0 || S.T[h] != 'G' || S.P[h].b != 1) { end = "U"; break; }
            printf("R %lld", S.W.b);
            for (int i = S.nx[h]; i >= 0; i = S.nx[i]) printf(" %c %lld", S.T[i], S.P[i].b);
            printf("\n");
        }
        printf("%s\n.\n", end); fflush(stdout);
    }
    return 0;
}
