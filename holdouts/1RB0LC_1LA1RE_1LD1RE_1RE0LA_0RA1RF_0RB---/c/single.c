/* single CAP: for each input line "WORD" (the tape from the head on, head in state C at the left end), run to the
 * next moment the head is in state C at the left end with the tape in single-number form
 *   X(n, t) = C> 000 (100)^n T   or   Y(n, t) = C> (100)^n T,   T = 1 (t = 0) or 101 (t = 1),
 * and print "X|Y n t STEPS EVENTS" (EVENTS: C-left-end moments passed on the way), "HALT STEPS" or "CAP STEPS".
 * Machine 1RB0LC_1LA1RE_1LD1RE_1RE0LA_0RA1RF_0RB---. */
#include "../../../tools/c/tm.h"
static int single(tm_tape *t, char *kind, long long *n, int *tt) {
    long long p = t->head, hi = t->hi;
    while (hi > p && tm_get(t, hi) == 0) hi--;
    *kind = 'Y';
    if (tm_get(t, p) == 0 && tm_get(t, p + 1) == 0 && tm_get(t, p + 2) == 0) { *kind = 'X'; p += 3; }
    long long k = 0;
    while (p + 2 <= hi && tm_get(t, p) == 1 && tm_get(t, p + 1) == 0 && tm_get(t, p + 2) == 0) { k++; p += 3; }
    if (p == hi && tm_get(t, p) == 1) { *n = k; *tt = 0; return k > 0; }
    if (p + 2 == hi && tm_get(t, p) == 1 && tm_get(t, p + 1) == 0 && tm_get(t, p + 2) == 1) { *n = k; *tt = 1; return k > 0; }
    return 0;
}
int main(int argc, char **argv) {
    tm_machine m; tm_parse("1RB0LC_1LA1RE_1LD1RE_1RE0LA_0RA1RF_0RB---", &m);
    long long cap = argc > 1 ? atoll(argv[1]) : 1000000000LL;
    static char line[1 << 22];
    while (fgets(line, sizeof line, stdin)) {
        long long n = (long long)strcspn(line, "\r\n");
        tm_tape t; tm_tape_init(&t, 8 * n + 4096);
        for (long long i = 0; i < n; i++) t.c[i + t.off] = (unsigned char)(line[i] - '0');
        t.head = 0; t.lo = 0; t.hi = n - 1;
        int st = 2, done = 0, tt; long long k = 0, ev = 0, nn; char kind;
        while (k < cap) {
            k++;
            if (!tm_step(&m, &t, &st)) { printf("HALT %lld\n", k); done = 1; break; }
            if (st == 2 && t.head == t.lo) {
                ev++;
                if (single(&t, &kind, &nn, &tt)) { printf("%c %lld %d %lld %lld\n", kind, nn, tt, k, ev); done = 1; break; }
            }
        }
        if (!done) printf("CAP %lld\n", k);
        fflush(stdout); tm_tape_free(&t);
    }
    return 0;
}
