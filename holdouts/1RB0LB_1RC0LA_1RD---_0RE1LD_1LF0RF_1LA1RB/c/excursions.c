/* excursions MACHINE MAX STATE L|R EVERY: each time the head, in STATE, stands on the left (L) or right (R) end of
   the visited cells, print "STEPS lo=LO hi=HI minhead=MIN maxhead=MAX": the extent of the head's excursion since the
   previous such moment (every EVERY-th moment).  Shared by the G01 machines studied with py/sweeps.py. */
#include "../../../tools/c/tm.h"
int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: excursions MACHINE MAX STATE L|R EVERY\n"); return 1; }
    tm_machine m; if (tm_parse(argv[1], &m)) return 1;
    long long max = atoll(argv[2]); int S = argv[3][0] - 'A', R = argv[4][0] == 'R'; long long E = atoll(argv[5]);
    tm_tape t; tm_tape_init(&t, 1 << 16); int st = 0;
    long long k = 0, mx = -(1LL << 62), mn = 1LL << 62, c = 0;
    while (k < max) {
        k++;
        if (!tm_step(&m, &t, &st)) { printf("HALT %lld\n", k); return 0; }
        if (t.head > mx) mx = t.head;
        if (t.head < mn) mn = t.head;
        if (st == S && t.head == (R ? t.hi : t.lo)) {
            if (c++ % E == 0) printf("%lld lo=%lld hi=%lld minhead=%lld maxhead=%lld\n", k, t.lo, t.hi, mn, mx);
            mx = -(1LL << 62); mn = 1LL << 62;
        }
    }
    return 0;
}
