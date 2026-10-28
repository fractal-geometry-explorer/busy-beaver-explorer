/* driver for the blank-run engine with integer positions (../blankrun/engine.h) */
#include <stdio.h>
#include <stdlib.h>
#include "../blankrun/engine.h"
#include "drv_common.h"
int main(int argc, char **argv) {
    int NR = argc > 1 ? atoi(argv[1]) : 8; static char line[1 << 16]; char t[256]; long long p[256], w; int n;
    while (fgets(line, sizeof line, stdin)) {
        if (!read_state(line, &w, t, p, &n)) { printf("bad input\n.\n"); continue; }
        nm = 0; halted = bad = 0; nend = 0; W = w;
        ins_at(0, 'G', 1);
        for (int i = 0; i < n; i++) ins_at(nm, t[i], p[i]);
        const char *end = "E";
        for (int r = 0; r < NR; r++) {
            do_round();
            if (halted) { end = "H"; break; }
            if (bad) { end = "U"; break; }
            printf("R %lld", (long long)W);
            for (int i = 1; i < nm; i++) printf(" %c %lld", T[i], (long long)P[i]);
            printf("\n");
        }
        printf("%s\n.\n", end); fflush(stdout);
    }
    return 0;
}
