/* evrun2 MACHINE STATE PREFIX CAP: like evrun, but the next event is the head in STATE at the left end of the visited
 * tape with the cells from the head on starting with PREFIX (a word of 0/1).  Prints "STEPS WORD", "HALT STEPS" or
 * "CAP STEPS" for each input line. */
#include "../../../tools/c/tm.h"
int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: evrun2 MACHINE STATE PREFIX CAP\n"); return 1; }
    tm_machine m;
    if (tm_parse(argv[1], &m)) { fprintf(stderr, "bad machine\n"); return 1; }
    int S = argv[2][0] - 'A'; const char *pf = argv[3]; int pl = (int)strlen(pf);
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
            if (st == S && t.head == t.lo) {
                int ok = 1;
                for (int i = 0; i < pl && ok; i++) ok = tm_get(&t, t.head + i) == pf[i] - '0';
                if (!ok) continue;
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
