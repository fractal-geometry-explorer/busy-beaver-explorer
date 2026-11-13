/* ctxev MACHINE STATE SYM CAP [list STEPS]
 * An *event* is: the head in STATE reading SYM with only 0s to its left (head at or left of the leftmost 1).
 * Default mode: for each input line (a word of 0/1: the tape from the head rightwards, 0s elsewhere, head in STATE on
 * its first cell) run to the next event and print "STEPS WORD" (WORD: the cells from the head to the rightmost 1),
 * "HALT STEPS" (STEPS counts the halting transition) or "CAP STEPS".
 * list mode: run from blank tape (state A) for STEPS steps and print every event as "STEPS WORD". */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int W[6][2], D[6][2], S[6][2];
static unsigned char *tape; static long long NT;
static long long pos, lo, hi; static int st;
/* one step; returns 0 on halt, -1 out of range */
static inline int step(void) {
    int b = tape[pos]; if (S[st][b] < 0) return 0;
    int w = W[st][b]; tape[pos] = w;
    if (w) { if (pos < lo) lo = pos; if (pos > hi) hi = pos; }
    else if (b) {
        if (lo == hi) { lo = NT; hi = -1; }
        else { if (pos == lo) { while (!tape[lo]) lo++; } if (pos == hi) { while (!tape[hi]) hi--; } }
    }
    pos += D[st][b]; st = S[st][b];
    if (pos < 4 || pos > NT - 4) return -1;
    return 1;
}
static void out(long long k) {
    printf("%lld ", k);
    long long z = hi > pos ? hi : pos;
    for (long long p = pos; p <= z; p++) putchar('0' + tape[p]);
    putchar('\n');
}
int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage\n"); return 1; }
    const char *m = argv[1];
    for (int i = 0; i < 6; i++) for (int b = 0; b < 2; b++) {
        const char *s = m + 7 * i + 3 * b;
        if (s[2] == '-') S[i][b] = -1; else { W[i][b] = s[0] - '0'; D[i][b] = s[1] == 'R' ? 1 : -1; S[i][b] = s[2] - 'A'; }
    }
    int ES = argv[2][0] - 'A', EB = argv[3][0] - '0'; long long cap = (long long)atof(argv[4]);
    if (argc > 6 && !strcmp(argv[5], "list")) {
        long long steps = (long long)atof(argv[6]);
        NT = 1LL << 27; tape = calloc(NT, 1); pos = NT / 2; lo = NT; hi = -1; st = 0;
        for (long long k = 1; k <= steps; k++) {
            int r = step();
            if (r == 0) { printf("HALT %lld\n", k); return 0; }
            if (r < 0) { printf("OUT %lld\n", k); return 0; }
            if (st == ES && hi >= 0 && pos <= lo && tape[pos] == EB) out(k);
        }
        return 0;
    }
    static char line[1 << 24];
    while (fgets(line, sizeof line, stdin)) {
        long long n = (long long)strcspn(line, "\r\n");
        NT = 64 * n + (1 << 20); tape = calloc(NT, 1); pos = NT / 2; lo = NT; hi = -1; st = ES;
        for (long long i = 0; i < n; i++) if (line[i] == '1') { tape[pos + i] = 1; if (lo == NT) lo = pos + i; hi = pos + i; }
        long long k = 0; int done = 0;
        while (k < cap) {
            k++;
            int r = step();
            if (r == 0) { printf("HALT %lld\n", k); done = 1; break; }
            if (r < 0) { printf("OUT %lld\n", k); done = 1; break; }
            if (st == ES && hi >= 0 && pos <= lo && tape[pos] == EB) { out(k); done = 1; break; }
        }
        if (!done) printf("CAP %lld\n", k);
        fflush(stdout); free(tape);
    }
    return 0;
}
