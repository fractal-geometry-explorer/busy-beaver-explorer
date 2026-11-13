/* ctxcount.c: how often the head of a machine run from blank tape is in state S with the word w at and right of the
 * head, for every w of K cells (K <= 8): the near misses of a halting context.  Shared by the G11 batch-4 folders.
 *
 *   gcc -O2 -o ctxcount ctxcount.c && ./ctxcount MACHINE MAX_STEPS STATE K [OFFSET]
 *
 * With OFFSET (default 0) the window starts OFFSET cells right of the head (-1: the cell left of the head first).
 *
 * Output: one line per word seen, "w count last_step", the cells read from the head rightwards.  Uses tools/c/tm.h.
 */
#include "../../../tools/c/tm.h"
int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: ctxcount MACHINE MAX_STEPS STATE K\n"); return 1; }
    tm_machine m; if (tm_parse(argv[1], &m)) { fprintf(stderr, "bad machine\n"); return 1; }
    long long max = (long long)atof(argv[2]); int S = argv[3][0] - 'A', K = atoi(argv[4]), off = argc > 5 ? atoi(argv[5]) : 0;
    static long long cnt[256], last[256];
    tm_tape t; tm_tape_init(&t, 1 << 20); int st = 0; long long k;
    for (k = 0; k < max; k++) {
        if (!tm_step(&m, &t, &st)) { printf("halted at step %lld\n", k + 1); break; }
        if (st != S) continue;
        int w = 0; for (int j = 0; j < K; j++) w = 2 * w + tm_get(&t, t.head + off + j);
        cnt[w]++; last[w] = k + 1;
    }
    for (int w = 0; w < (1 << K); w++) if (cnt[w]) {
        for (int j = K - 1; j >= 0; j--) putchar('0' + ((w >> j) & 1));
        printf(" %lld %lld\n", cnt[w], last[w]);
    }
    return 0;
}
