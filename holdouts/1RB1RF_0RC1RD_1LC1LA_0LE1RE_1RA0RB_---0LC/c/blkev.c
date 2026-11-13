/* blkev MACHINE MAX_STEPS STATE G T [K]
 * Print the tape right of the "wall" each time the head, in STATE, has exactly G zeros on its left and then a run of
 * at least T ones (the wall).  Output: "STEPS WALL | tape right of the wall, run-length coded, head marked S>x".
 * Used for the passes of the 1RB0LA_1RC--- family (holdouts/<M>/py/passmap.py).  Build: gcc -O2 -o blkev blkev.c
 */
#include "../../../tools/c/tm.h"
static void put(int c, long long run) { if (run > 1) printf(" %d^%lld", c, run); else if (run == 1) printf(" %d", c); }
int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: blkev MACHINE MAX_STEPS STATE G T [K]\n"); return 1; }
    tm_machine m; if (tm_parse(argv[1], &m)) { fprintf(stderr, "bad machine\n"); return 1; }
    long long max = atoll(argv[2]); int S = argv[3][0] - 'A'; int G = atoi(argv[4]); long long T = atoll(argv[5]);
    long long K = argc > 6 ? atoll(argv[6]) : 1000000000LL;
    tm_tape t; tm_tape_init(&t, 1 << 20); int st = 0; long long k = 0, lines = 0, b0 = 0;
    while (k < max && lines < K) {
        k++;
        if (!tm_step(&m, &t, &st)) { printf("HALT %lld\n", k); break; }
        if (st != S) continue;
        long long h = t.head; int ok = 1;
        for (int i = 1; i <= G; i++) if (tm_get(&t, h - i)) { ok = 0; break; }
        if (!ok || !tm_get(&t, h - G - 1) || !tm_get(&t, h - G - T)) continue;
        for (long long j = 1; j < T; j += 7) if (!tm_get(&t, h - G - 1 - j)) { ok = 0; break; }
        if (!ok) continue;
        long long b;   /* left end of the wall: cached, the wall only grows at its right end */
        if (b0 && !tm_get(&t, b0) && tm_get(&t, b0 + 1) && b0 < h - G - 1) b = b0;
        else { b = h - G - 1; while (tm_get(&t, b)) b--; }
        b0 = b;
        printf("%lld %lld |", k, h - G - 1 - b);
        int cur = -1; long long run = 0;
        for (long long p = h - G; p <= t.hi; p++) {
            int c = tm_get(&t, p);
            if (p == h) { put(cur, run); run = 0; cur = -1; printf(" %c>%d", 'A' + st, c); continue; }
            if (c == cur) run++; else { put(cur, run); cur = c; run = 1; }
        }
        put(cur, run); printf("\n"); lines++;
    }
    return 0;
}
