/* windowscan: every tape that is a word of K cells in blank tape, the head on the word's first cell in a given state,
 * run for at most T steps; counts the words whose run halts, leaves the window, or neither.  An example of the parts
 * protocol (parts.h), and a check on which short words lead to a halt.
 *
 *   windowscan MACHINE STATE K T [PART NPARTS]
 *
 * Writes: sum words, sum halted, sum escaped (the head left the K cells before a halt), sum timeout, max halt_steps
 * (with the word, cell 0 first), and an event for each halting word when K <= 12.
 */
#include "tm.h"
#include "parts.h"

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: windowscan MACHINE STATE K T [PART NPARTS]\n"); return 1; }
    tm_machine m;
    if (tm_parse(argv[1], &m)) { fprintf(stderr, "bad machine\n"); return 1; }
    int st0 = argv[2][0] - 'A', K = atoi(argv[3]); long long T = atoll(argv[4]);
    parts_args(argc, argv, 5);
    if (K < 1 || K > 40 || st0 < 0 || st0 >= m.n) { fprintf(stderr, "bad STATE or K\n"); return 1; }
    long long words = 0, halted = 0, escaped = 0, timeout = 0, best = -1; unsigned long long bestw = 0;
    tm_tape t; tm_tape_init(&t, 1 << 12);
    for (unsigned long long w = 0; w < (1ULL << K); w++) {
        if (!parts_owns(w)) continue;
        words++;
        memset(t.c, 0, (size_t)t.size); t.head = t.lo = t.hi = 0;
        for (int i = 0; i < K; i++) t.c[t.off + i] = (w >> i) & 1;
        int st = st0, h = 0; long long k = 0, out = 0;
        while (k < T) {
            k++;
            if (!tm_step(&m, &t, &st)) { h = 1; break; }
            if (t.head < 0 || t.head >= K) { out = 1; break; }
        }
        if (h) {
            halted++;
            if (k > best) { best = k; bestw = w; }
            if (K <= 12) { char s[64]; for (int i = 0; i < K; i++) s[i] = '0' + ((w >> i) & 1); s[K] = 0; parts_event("halt %s %lld", s, k); }
        } else if (out) escaped++; else timeout++;
    }
    parts_sum("words", words); parts_sum("halted", halted); parts_sum("escaped", escaped); parts_sum("timeout", timeout);
    if (best >= 0) { char s[64]; for (int i = 0; i < K; i++) s[i] = '0' + ((bestw >> i) & 1); s[K] = 0; parts_max("halt_steps", best, "%s", s); }
    parts_done();
    tm_tape_free(&t);
    return 0;
}
