/* forbid.c: run a machine from blank tape and report the first step at which one of the given words appears on
 * the tape (as cells, left to right), or that none appears within MAX_STEPS.  Shared by the G11 batch-4 folders.
 *
 *   gcc -O2 -o forbid forbid.c && ./forbid MACHINE MAX_STEPS WORD [WORD ...]      e.g. ./forbid M 1e10 111
 *
 * A WORD `S:w` (a state letter, a colon, cells) is a head context instead: the head in state S on the first cell of
 * w, w on the cells from the head rightwards; it is checked after every step, and the tape is printed when found.  With FROM=N in the environment,
 * occurrences before step N are ignored (the last one before N is reported as "last before").
 *
 * A word can only appear when a cell changes, so after each write that changes a cell every window of each word's
 * length containing that cell is compared.  Output: "WORD found at step N, position P" or "none of WORDs in N steps"
 * (plus the run's final width and ones).  Uses tools/c/tm.h (the shared, tested simulator).
 */
#include "../../../tools/c/tm.h"
#include <math.h>
int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: forbid MACHINE MAX_STEPS WORD...\n"); return 1; }
    tm_machine m; if (tm_parse(argv[1], &m)) { fprintf(stderr, "bad machine\n"); return 1; }
    long long max = (long long)atof(argv[2]);
    long long from = getenv("FROM") ? (long long)atof(getenv("FROM")) : 0, lastb = -1;
    int nw = argc - 3; char **w = argv + 3;
    tm_tape t; tm_tape_init(&t, 1 << 20); int st = 0; long long k = 0;
    for (k = 0; k < max; k++) {
        long long p = t.head; int before = tm_get(&t, p);
        if (!tm_step(&m, &t, &st)) { printf("halted at step %lld\n", k + 1); return 0; }
        for (int i = 0; i < nw; i++) {
            if (w[i][1] != ':') continue;
            if (st != w[i][0] - 'A') continue;
            int ok = 1;
            for (int j = 0; w[i][2 + j] && ok; j++) ok = tm_get(&t, t.head + j) == w[i][2 + j] - '0';
            if (ok) {
                if (k + 1 < from) { lastb = k + 1; continue; }
                printf("%s found at step %lld: ", w[i], k + 1); tm_print(&m, &t, st, stdout); return 0;
            }
        }
        if (tm_get(&t, p) == before) continue;
        for (int i = 0; i < nw; i++) {
            if (w[i][1] == ':') continue;
            int L = (int)strlen(w[i]);
            for (long long s = p - L + 1; s <= p; s++) {
                int ok = 1;
                for (int j = 0; j < L && ok; j++) ok = tm_get(&t, s + j) == w[i][j] - '0';
                if (ok && k + 1 < from) { lastb = k + 1; ok = 0; }
                if (ok) { printf("%s found at step %lld, position %lld\n", w[i], k + 1, s); return 0; }
            }
        }
    }
    if (lastb >= 0) printf("last before %lld: step %lld\n", from, lastb);
    printf("none of the words in %lld steps; width %lld, ones %lld\n", k, t.hi - t.lo + 1, tm_ones(&t));
    return 0;
}
