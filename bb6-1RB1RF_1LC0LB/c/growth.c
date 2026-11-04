/* growth: the width, the number of 1s and the number of left-end extensions of the run from blank tape at steps
 * 10, 20, 50, 100, 200, 500, ... up to MAX_STEPS.  A left-end extension is counted once per run of extensions on
 * the left side (the head reaching a new cell on the left after it last reached one on the right, or at the start).
 *
 *   gcc -O2 -o growth bb6-1RB1RF_1LC0LB/c/growth.c && ./growth 1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE--- 10000000000
 *
 * Output lines "STEPS WIDTH ONES LEFT_EXTENSIONS"; runs/growth_1e10.txt is the output to 10^10 (about a minute).
 */
#include "../../tools/c/tm.h"

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: growth MACHINE MAX_STEPS\n"); return 1; }
    tm_machine m;
    if (tm_parse(argv[1], &m)) { fprintf(stderr, "bad machine %s\n", argv[1]); return 1; }
    long long max = atoll(argv[2]);
    tm_tape t; tm_tape_init(&t, 1 << 16);
    int st = 0, mi = 0; const int mult[3] = {1, 2, 5};
    long long k = 0, base = 10, next = 10, lext = 0; char last = 0;
    while (k < max) {
        long long lo = t.lo, hi = t.hi;
        k++;
        if (!tm_step(&m, &t, &st)) { printf("HALT %lld\n", k); return 0; }
        if (t.lo < lo) { if (last != 'L') lext++; last = 'L'; }
        else if (t.hi > hi) last = 'R';
        if (k == next) {
            printf("%lld %lld %lld %lld\n", k, t.hi - t.lo + 1, tm_ones(&t), lext);
            if (++mi == 3) { mi = 0; base *= 10; }
            next = base * mult[mi];
        }
    }
    tm_tape_free(&t);
    return 0;
}
