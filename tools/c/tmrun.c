/* tmrun: run a machine from blank tape.
 *
 *   tmrun MACHINE MAX_STEPS                 one line: "halted STEPS ONES" or "running STEPS ONES"
 *   tmrun MACHINE MAX_STEPS records [K]     also the tape (tm_print) each time the head reaches a new cell, at most K
 *                                           lines (default 200): "STEPS L|R WIDTH tape"
 *   tmrun MACHINE MAX_STEPS every N         the tape every N steps
 *   tmrun MACHINE MAX_STEPS at S L|R [K]    the tape each time the head, in state S, is at the left (L) or right (R)
 *                                           end of the visited cells, at most K lines (default 200): "STEPS tape"
 *
 * Steps follow the bbchallenge count (the halting transition is a step).
 */
#include "tm.h"

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: tmrun MACHINE MAX_STEPS [records [K] | every N | at S L|R [K]]\n"); return 1; }
    tm_machine m;
    if (tm_parse(argv[1], &m)) { fprintf(stderr, "bad machine %s\n", argv[1]); return 1; }
    long long max = atoll(argv[2]);
    int mode = 0; long long arg = 200;
    if (argc > 3 && !strcmp(argv[3], "records")) { mode = 1; if (argc > 4) arg = atoll(argv[4]); }
    if (argc > 3 && !strcmp(argv[3], "every")) { mode = 2; arg = argc > 4 ? atoll(argv[4]) : 1; }
    int ast = 0, aside = 0;
    if (argc > 5 && !strcmp(argv[3], "at")) { mode = 3; ast = argv[4][0] - 'A'; aside = argv[5][0] == 'R'; if (argc > 6) arg = atoll(argv[6]); }
    tm_tape t; tm_tape_init(&t, 1 << 16);
    int st = 0, halted = 0; long long k = 0, lines = 0;
    if (mode == 0) k = tm_run(&m, &t, &st, max, &halted);
    else {
        while (k < max) {
            long long lo = t.lo, hi = t.hi;
            k++;
            if (!tm_step(&m, &t, &st)) { halted = 1; break; }
            if (mode == 1 && lines < arg && (t.lo < lo || t.hi > hi)) {
                printf("%lld %c %lld ", k, t.lo < lo ? 'L' : 'R', t.hi - t.lo); tm_print(&m, &t, st, stdout); lines++;
            }
            if (mode == 2 && k % arg == 0) { printf("%lld ", k); tm_print(&m, &t, st, stdout); }
            if (mode == 3 && lines < arg && st == ast && t.head == (aside ? t.hi : t.lo)) {
                printf("%lld ", k); tm_print(&m, &t, st, stdout); lines++;
            }
        }
    }
    printf("%s %lld %lld\n", halted ? "halted" : "running", k, tm_ones(&t));
    tm_tape_free(&t);
    return 0;
}
