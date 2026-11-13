/* walls MACHINE STEPS: run a machine of the wall-counter family from blank tape and read its tape at every sample
 * point (head at the left end of the visited tape, state D, reading 1) as runs of the block 1000 and the words
 * between them ("walls").  A sample is ordinary when every wall is one of 1001 1001100 100110 10011 10010 0 and the tape
 * ends with 1001.  Counts the samples, the overflows (an ordinary sample with every wall at 10011 followed by one that
 * is not ordinary), the mergers (any other ordinary -> not ordinary change), and the transitions E1; prints JSON.
 * Uses tools/c/tm.h. */
#include "../../../tools/c/tm.h"
static const char *P[6] = {"1001", "1001100", "100110", "10011", "10010", "0"};
static char wall[1 << 16];
int main(int argc, char **argv) {
    tm_machine m; if (argc < 3 || tm_parse(argv[1], &m)) { fprintf(stderr, "usage: walls MACHINE STEPS\n"); return 1; }
    long long max = atoll(argv[2]), k = 0, samples = 0, ov = 0, col = 0, e1 = 0, f1 = 0, halted = 0;
    int prev_std = 0, prev_all3 = 0, nwalls = 0; long long last_step = 0;
    static char lastline[1 << 20]; lastline[0] = 0;
    tm_tape t; tm_tape_init(&t, 1 << 20); int st = 0;
    while (k < max) {
        int y = tm_get(&t, t.head);
        if (st == 4 && y == 1) e1++;
        if (st == 5 && y == 1) f1++;
        if (!tm_step(&m, &t, &st)) { halted = k + 1; break; }
        k++;
        if (st == 3 && t.head == t.lo && tm_get(&t, t.head) == 1) {
            samples++;
            int std = 1, all3 = 1, nw = 0, wl = 0, first = 1; long long run = 0; int o = 0;
            long long p = t.lo;
            while (p <= t.hi) {
                if (p + 3 <= t.hi && tm_get(&t, p) == 1 && !tm_get(&t, p + 1) && !tm_get(&t, p + 2) && !tm_get(&t, p + 3)) {
                    if (wl) {  /* a wall ends */
                        wall[wl] = 0; int ok = 0;
                        for (int i = 0; i < 6; i++) if (!strcmp(wall, P[i])) ok = 1;
                        if (first) std = 0;
                        if (!ok) std = 0;
                        if (strcmp(wall, "10011")) all3 = 0;
                        nw++;
                        if (o < (1 << 19)) o += snprintf(lastline + o, (1 << 20) - o, " %s", wall);
                        wl = 0;
                    }
                    run++; p += 4; first = 0; continue;
                }
                if (run) { if (o < (1 << 19)) o += snprintf(lastline + o, (1 << 20) - o, " c^%lld", run); run = 0; }
                if (wl < (1 << 16) - 1) wall[wl++] = '0' + tm_get(&t, p);
                p++;
            }
            if (run) { std = 0; }
            wall[wl] = 0;
            if (strcmp(wall, "1001")) std = 0;
            if (o < (1 << 19)) o += snprintf(lastline + o, (1 << 20) - o, " %s", wall);
            if (prev_std && !std) { if (prev_all3) ov++; else col++; }
            prev_std = std; prev_all3 = all3; nwalls = nw; last_step = k;
        }
    }
    printf("{\"machine\": \"%s\", \"steps\": %lld, \"halted\": %lld, \"samples\": %lld, \"overflows\": %lld, "
           "\"collisions\": %lld, \"e1\": %lld, \"f1\": %lld, \"walls_end\": %d, \"sample\": {\"step\": %lld, \"text\": \"%s\"}}\n",
           argv[1], k, halted, samples, ov, col, e1, f1, nwalls, last_step, lastline + 1);
    return 0;
}
