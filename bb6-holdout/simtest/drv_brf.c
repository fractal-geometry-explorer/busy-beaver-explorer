/* driver for the fast blank-run engine (../blankrun/fast.h) */
#include <stdio.h>
#include <stdlib.h>
#include "../blankrun/fast.h"
#include "drv_common.h"
int main(int argc, char **argv) {
    int NR = argc > 1 ? atoi(argv[1]) : 8; static char line[1 << 16]; char t[256]; long long p[256], w; int n;
    while (fgets(line, sizeof line, stdin)) {
        if (!read_state(line, &w, t, p, &n)) { printf("bad input\n.\n"); continue; }
        set_start(w); halted = bad = 0; nend = 0;
        add_mark(tG, 1);
        for (int i = 0; i < n; i++) add_mark(t[i] == 'M' ? tM : t[i] == 'W' ? tW : t[i] == 'B' ? tB : tG, p[i]);
        const char *end = "E";
        for (int r = 0; r < NR; r++) {
            do_round();
            if (halted) { end = "H"; break; }
            if (bad) { end = "U"; break; }
            printf("R %lld", (long long)realW());
            for (int i = 1; i < nm; i++) printf(" %c %lld", "GMWB"[MT(i)], (long long)realP(i));
            printf("\n");
        }
        printf("%s\n.\n", end); fflush(stdout);
    }
    return 0;
}
