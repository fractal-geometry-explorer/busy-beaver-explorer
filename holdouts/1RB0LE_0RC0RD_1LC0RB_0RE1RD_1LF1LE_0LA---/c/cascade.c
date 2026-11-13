/* cascade: iterate the halving-cascade map of 1RB0LE_0RC0RD_1LC0RB_0RE1RD_1LF1LE_0LA--- (see ../py/cascade.py) from
 * the list (1, 1) that the run from blank tape reaches at step 13, and report a block 0 (a halt of the machine, if the
 * map is exact) or statistics.
 *
 *   gcc -O2 -o cascade cascade.c && ./cascade MAPSTEPS [REPORT_EVERY]
 */
#include <stdio.h>
#include <stdlib.h>
#define K 4096
static long long ns[K];
static int k;
int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: cascade MAPSTEPS [REPORT_EVERY]\n"); return 1; }
    long long N = atoll(argv[1]), every = argc > 2 ? atoll(argv[2]) : 100000000LL;
    k = 2; ns[0] = 1; ns[1] = 1;
    long long ends = 0, minodd = -1;
    setvbuf(stdout, NULL, _IOLBF, 0);
    for (long long it = 1; it <= N; it++) {
        if (ns[0] == 1) {                       /* merge: (1, x, y, ...) -> (x+3, y+1, ...) */
            ns[1] += 3;
            for (int i = 0; i + 1 < k; i++) ns[i] = ns[i + 1];
            k--;
            if (k >= 2) ns[1] += 1; else ns[k++] = 1;
        } else {                                /* the cascade */
            long long v = ns[0]; int i = 0;
            for (;;) {
                long long h = v / 2, c = v - h;
                ns[i] = h;
                if (h == 0) { printf("ZERO at map step %lld (block %d of %d)\n", it, i, k); return 0; }
                if (v & 1) {
                    while (k < i + 3) ns[k++] = 0;
                    ns[i + 1] += c + 2; ns[i + 2] += 1;
                    break;
                }
                if (i + 1 >= k) {               /* past the last block, with carry c */
                    ends++;
                    long long o = c; while (!(o & 1)) o >>= 1;
                    if (minodd < 0 || o < minodd) minodd = o;
                    ns[k++] = 0;
                    if (k >= K - 4) { printf("list too long\n"); return 1; }
                }
                v = ns[i + 1] + c; i++;
            }
        }
        if (it % every == 0) {
            long long s = 0, mx = 0;
            for (int i = 0; i < k; i++) { s += ns[i]; if (ns[i] > mx) mx = ns[i]; }
            printf("step %lld: %d blocks, sum %lld, max %lld, cascades past the end %lld, smallest odd part of a "
                   "carry there %lld\n", it, k, s, mx, ends, minodd);
        }
    }
    return 0;
}
