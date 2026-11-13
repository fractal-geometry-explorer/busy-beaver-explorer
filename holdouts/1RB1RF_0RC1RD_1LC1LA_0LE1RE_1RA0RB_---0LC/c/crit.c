/* crit MACHINE MAX_STEPS STATE [show]
 * Count the configurations in which the head, in STATE, reads a 0, sorted by the three cells right of the head
 * (first and last step of each kind).  With `show`, also print the tape (run-length coded) at each of them.
 * For the 1RB0LA_1RC--- family: lean/HaltIff.lean proves that the machine halts iff the run reaches the critical
 * configuration (D>0 0 1 for 1RB0LA_1RC---_0LD1RD_0RA0RE_0RF1RC_1LF0LA, D>0 1 for
 * 1RB0LA_1RC---_0LD1RD_0RB0RE_0RF0LD_1LF0LA, E>0 1 0 for 1RB1RF_0RC1RD_1LC1LA_0LE1RE_1RA0RB_---0LC); this lists
 * how often the state reads a 0 at all, and what is next to it.
 * Build (from the repository root): gcc -O2 -o /tmp/crit holdouts/<M>/c/crit.c
 */
#include "../../../tools/c/tm.h"
int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: crit MACHINE MAX_STEPS STATE [show]\n"); return 1; }
    tm_machine m; if (tm_parse(argv[1], &m)) { fprintf(stderr, "bad machine\n"); return 1; }
    long long max = atoll(argv[2]); int S = argv[3][0] - 'A', show = argc > 4;
    tm_tape t; tm_tape_init(&t, 1 << 20); int st = 0; long long k = 0, cnt[8] = {0}, first[8] = {0}, last[8] = {0};
    while (k < max) {
        k++;
        if (!tm_step(&m, &t, &st)) { printf("HALT %lld\n", k); break; }
        if (st == S && !tm_get(&t, t.head)) {
            int c = tm_get(&t, t.head + 1) * 4 + tm_get(&t, t.head + 2) * 2 + tm_get(&t, t.head + 3);
            cnt[c]++; if (!first[c]) first[c] = k; last[c] = k;
            if (show) { printf("%lld ", k); tm_print(&m, &t, st, stdout); }
        }
    }
    long long tot = 0;
    for (int c = 0; c < 8; c++) {
        tot += cnt[c];
        printf("%c>0 %d %d %d: %lld times, first step %lld, last step %lld\n", 'A' + S, c >> 2, (c >> 1) & 1, c & 1, cnt[c], first[c], last[c]);
    }
    printf("total %lld in %lld steps\n", tot, k);
    return 0;
}
