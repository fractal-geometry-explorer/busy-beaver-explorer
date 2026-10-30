/* orbitck: checkpoints of the super orbit for the chunked Lean check of lean/orbit/ (written by lean/orbit_gen.py).
 *
 *   orbitck EVERY COUNT
 *
 * runs the super step of lean/Wave.lean (`superL`) with the step count of lean/WaveTime.lean (`superT`) from the tape
 * [1, 6, 5, 0] at machine step 136, and prints "S T p_m ... p_1" after every EVERY super steps, COUNT times: the
 * list nearest first, as in Lean.  Nothing here is trusted: Lean recomputes every super step between checkpoints.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned long long u64;
typedef unsigned __int128 u128;

#define MAXB 4096
static u64 L[MAXB], W[MAXB];
static int n;

static void put128(u128 v) {
    char s[64];
    int k = 63;
    s[k] = 0;
    if (v == 0) s[--k] = '0';
    while (v > 0) { s[--k] = (char)('0' + (int)(v % 10)); v /= 10; }
    fputs(s + k, stdout);
}

/* One super step on L[0..n) (nearest first); returns its machine steps, or 0 on a halt. */
static u128 super(void) {
    u64 d = L[0] + 10, A = 3;
    u128 t = 200;
    int i = 1, w = 0;                     /* L[i] is the next block to the left; W the new blocks, nearest first */
    for (;;) {
        u64 q = d / 2;
        if (d % 2) {
            t += (u128)2 * q * q + 4 * q + 17 + A;
            W[w++] = (d + 5) / 2;
            if (i < n) { W[w++] = L[i] + (d - 1) / 2; i++; }
            else W[w++] = (d - 1) / 2;
            break;
        }
        if (i >= n && d == 4) return 0;
        t += (u128)2 * q * q + q - 5;
        A += q + 1;
        W[w++] = q;
        d = (i < n ? L[i++] : 0) + q;
        if (w + 2 >= MAXB) { fprintf(stderr, "too many blocks\n"); exit(2); }
    }
    while (i < n) W[w++] = L[i++];
    memcpy(L, W, sizeof(u64) * w);
    n = w;
    return t;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: orbitck EVERY COUNT\n"); return 1; }
    u64 every = strtoull(argv[1], 0, 10), count = strtoull(argv[2], 0, 10), s = 0;
    u128 T = 136;
    n = 2; L[0] = 6; L[1] = 1;
    for (u64 c = 0; c < count; c++) {
        for (u64 k = 0; k < every; k++) {
            u128 t = super();
            if (!t) { printf("halt "); put128(T); printf("\n"); return 0; }
            T += t;
        }
        s += every;
        printf("%llu ", s);
        put128(T);
        for (int j = 0; j < n; j++) printf(" %llu", L[j]);
        printf("\n");
        fflush(stdout);
    }
    return 0;
}
