/* ensemble: the super step of 1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB from many random starts, for testing the
 * halting heuristic on the map itself (py/top_stats.py reads the output).
 *
 *   ensemble ORBITS SUPER_STEPS SEED MIN_BLOCKS MAX_BLOCKS MAX_BLOCK FIRST_ID
 *
 * Each orbit starts from the tape [p_1, ..., p_m, 5, 0] with m uniform in MIN_BLOCKS..MAX_BLOCKS and each p_l uniform
 * in 1..MAX_BLOCK (xorshift64 from SEED), and runs SUPER_STEPS super steps directly (no tables), as in c/superrun.c
 * -d: level 0 = p_m receives a wave h = 10; d = p + h odd turns (the block becomes (d + 5)/2, the level above gains
 * (d - 1)/2), d even passes d/2 on.  The top level always passes on to the left end (py/waves.py `superstep`).
 *
 * Output: "start ID p_1,...,p_m" for each orbit, then "R ID S m d1 H" at each return to the left end: super step S
 * (from 1), m blocks before it, d1 = N / 2^(m-1), and H = 1 if d1 is a power of two (the halt; the orbit stops there),
 * else 0.  "overflow ID" if a value passes 2^62 (the orbit is dropped).  tests/test_top.py checks it against waves.py.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

typedef uint64_t u64;

static u64 rs;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

#define MAXM 400

int main(int argc, char **argv) {
    if (argc < 8) {
        fprintf(stderr, "usage: ensemble ORBITS SUPER_STEPS SEED MIN_BLOCKS MAX_BLOCKS MAX_BLOCK FIRST_ID\n");
        return 1;
    }
    long n = atol(argv[1]), id0 = atol(argv[7]);
    u64 budget = strtoull(argv[2], 0, 10), vmax = strtoull(argv[6], 0, 10);
    int lo = atoi(argv[4]), hi = atoi(argv[5]);
    rs = strtoull(argv[3], 0, 10) * 2654435761ULL + 12345;
    static u64 lv[MAXM];
    for (long id = id0; id < id0 + n; id++) {
        int m = lo + (int)(rnd() % (u64)(hi - lo + 1));
        for (int i = m - 1; i >= 0; i--) lv[i] = 1 + rnd() % vmax;
        printf("start %ld ", id);
        for (int i = m - 1; i >= 0; i--) printf("%llu%s", (unsigned long long)lv[i], i ? "," : "\n");
        for (u64 S = 1; S <= budget; S++) {
            u64 h = 10;
            int k = 0;
            for (;;) {
                u64 d = lv[k] + h;
                if (d > (1ULL << 62)) { printf("overflow %ld\n", id); goto next; }
                if (k == m - 1) {
                    int s = __builtin_ctzll(d);
                    u64 u = d >> s;
                    printf("R %ld %llu %d %llu %d\n", id, (unsigned long long)S, m, (unsigned long long)d, u == 1);
                    if (u == 1) goto next;
                    if (m + s + 1 >= MAXM) { printf("overflow %ld\n", id); goto next; }
                    m--;
                    for (int t = s - 1; t >= 0; t--) lv[m++] = u << t;
                    lv[m++] = (u + 5) / 2;
                    lv[m++] = (u - 1) / 2;
                    break;
                }
                if (d & 1) { lv[k] = (d + 5) / 2; lv[k + 1] += (d - 1) / 2; break; }
                lv[k] = h = d / 2;
                k++;
            }
        }
    next:;
    }
    return 0;
}
