/* evrun MACHINE STATE READ CAP: for each line of stdin (a word of 0/1: the tape from the head to the right, the
 * head at its first cell in STATE, blank elsewhere), run until the head is again in STATE at the left end of the
 * visited tape reading READ, and print "STEPS WORD" (the tape from the head to the right end, trailing 0s cut),
 * "HALT STEPS" or "CAP STEPS".  Used by ../py/rounds.py.  Steps follow bbchallenge (the halting step counts). */
#include "../../../tools/c/tm.h"
int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: evrun MACHINE STATE READ CAP\n"); return 1; }
    tm_machine m;
    if (tm_parse(argv[1], &m)) { fprintf(stderr, "bad machine\n"); return 1; }
    int S = argv[2][0] - 'A', X = atoi(argv[3]);
    long long cap = atoll(argv[4]);
    static char line[1 << 22];
    while (fgets(line, sizeof line, stdin)) {
        long long n = (long long)strcspn(line, "\r\n");
        tm_tape t; tm_tape_init(&t, 4 * n + 4096);
        for (long long i = 0; i < n; i++) t.c[i + t.off] = (unsigned char)(line[i] - '0');
        t.head = 0; t.lo = 0; t.hi = n > 0 ? n - 1 : 0;
        int st = S; long long k = 0; int done = 0;
        while (k < cap) {
            k++;
            if (!tm_step(&m, &t, &st)) { printf("HALT %lld\n", k); done = 1; break; }
            if (st == S && t.head == t.lo && tm_get(&t, t.head) == X) {
                long long hi = t.hi;
                while (hi > t.head && tm_get(&t, hi) == 0) hi--;
                printf("%lld ", k);
                for (long long p = t.head; p <= hi; p++) putchar('0' + tm_get(&t, p));
                putchar('\n'); done = 1; break;
            }
        }
        if (!done) printf("CAP %lld\n", k);
        fflush(stdout);
        tm_tape_free(&t);
    }
    return 0;
}
