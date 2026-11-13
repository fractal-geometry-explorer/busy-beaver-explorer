/* passes: the passes of the marker of 1RB1RF_1RC0LD_1LB1RA_1RE1LE_0RC0LB_0RB---.
 *
 *   gcc -O2 -o passes holdouts/1RB1RF_1RC0LD_1LB1RA_1RE1LE_0RC0LB_0RB---/c/passes.c && ./passes MAX_STEPS
 *
 * At every turn of the head at the right end of the tape (the head within 3 cells of it, turning left), the gap is
 * the distance from the head back to the nearest 0 on its left (the marker).  While the marker zig-zags towards the
 * end the gap shrinks; when it jumps up a new marker has been launched.  Each jump prints
 *   STEPS W=width prevgap=.. gap=.. st=STATE | the tape left of the marker (run-length coded) | rest CELLS
 * A halt prints "STEPS HALT".
 */
#include "../../../tools/c/tm.h"

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: passes MAX_STEPS\n"); return 1; }
    tm_machine m;
    tm_parse("1RB1RF_1RC0LD_1LB1RA_1RE1LE_0RC0LB_0RB---", &m);
    long long to = atoll(argv[1]);
    tm_tape t; tm_tape_init(&t, 1 << 16);
    int st = 0, lastd = 0; long long k = 0, pg = -1;
    while (k < to) {
        long long h = t.head; k++;
        if (!tm_step(&m, &t, &st)) { printf("%lld HALT\n", k); return 0; }
        int d = t.head > h ? 1 : -1;
        if (lastd == 1 && d == -1 && t.hi - t.head <= 3) {
            long long p = t.head - 1;
            while (p >= t.lo && tm_get(&t, p) == 1) p--;
            long long g = t.head - p;
            if (pg >= 0 && g > pg) {
                printf("%lld W=%lld prevgap=%lld gap=%lld st=%c | ", k, t.hi - t.lo + 1, pg, g, 'A' + st);
                long long q = t.lo;
                while (q <= p) {
                    int v = tm_get(&t, q); long long r = q;
                    while (r <= p && tm_get(&t, r) == v) r++;
                    if (r - q > 1) printf("%d^%lld ", v, r - q); else printf("%d ", v);
                    q = r;
                }
                printf("| rest %lld\n", t.hi - p);
            }
            pg = g;
        }
        lastd = d;
    }
    printf("running %lld\n", k);
    return 0;
}
