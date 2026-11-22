/* pbvis MACHINE START COUNT [EVERY]
   Direct simulation of 1RB---_1LC0LC_1RD1LB_1LE1RD_0LA1LF_1LD0RF (or any machine) from blank tape.  From step START
   on, at each "round start" (state B on the leftmost visited cell, and the cells from the head reading 0 1^7 0: the
   prefix form P_b), counts the visit; prints "step cells" for visit 0, EVERY, 2*EVERY, ... until COUNT visits.
   cells: the tape from the head to the rightmost visited cell. */
#include "../../../tools/c/tm.h"
int main(int argc, char **argv) {
    tm_machine m; tm_parse(argv[1], &m);
    long long start = (long long)atof(argv[2]), count = atoll(argv[3]), every = argc > 4 ? atoll(argv[4]) : 1;
    tm_tape t; tm_tape_init(&t, 1 << 22); int st = 0; long long vis = 0; static const char pat[] = "011111110";
    char *buf = NULL; long long bufn = 0;
    for (long long k = 1;; k++) {
        if (!tm_step(&m, &t, &st)) { printf("HALT %lld\n", k); return 0; }
        if (k >= start && st == 1 && t.head == t.lo) {
            int ok = 1;
            for (int i = 0; i < 9; i++) if (tm_get(&t, t.head + i) != pat[i] - '0') { ok = 0; break; }
            if (!ok) continue;
            if (vis % every == 0) {
                long long n = t.hi - t.head + 1;
                if (n + 2 > bufn) { bufn = 2 * n + 16; buf = realloc(buf, bufn); }
                for (long long p = 0; p < n; p++) buf[p] = '0' + tm_get(&t, t.head + p);
                buf[n] = 0; printf("%lld %s\n", k, buf); fflush(stdout);
            }
            if (++vis >= count) return 0;
        }
    }
}
