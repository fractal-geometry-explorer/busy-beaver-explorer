/* bottom2adic: N mod 2^k over one exact period of the last k blocks of the super orbit.
 *
 *   bottom2adic K WARMUP PERIOD p_m p_(m-1) ... (at least K blocks, the last block first)
 *
 * N mod 2^K = (10 + sum_j lv[j] 2^j) mod 2^K depends only on the last K blocks (lv[0] = p_m), and they run on their
 * own (lean/Cascade.lean, `superL_split`).  The program runs them alone for WARMUP super steps, then for PERIOD more,
 * histogramming N mod 2^K, and checks that the blocks are back where the PERIOD began (so the histogram is the exact
 * time average for all later super steps).  For each b <= K it prints, from the histogram mod 2^b: the mean of
 * |P(bit b-1 = 1 | the bits below) - 1/2| over the visited classes (weighted by time), the classes mod 2^(b-1) never
 * visited, and the least and largest frequency of a nonzero residue mod 2^b relative to uniform; then the frequency of
 * v2(N) = j relative to 2^-(j+1), and every residue mod 2^K that never occurs.
 *
 * With blocks from runs/superrun_checkpoints.txt (super step 10^9) and the periods of runs/superrun_long.txt, e.g.
 *   bottom2adic 18 1000000000 1048576000 $(tail -1 runs/superrun_checkpoints.txt | awk '{for(i=NF;i>2;i--) printf "%s ",$i}')
 * (about 30 s) gives runs/bottom2adic_18.txt.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>

typedef uint64_t u64;

static int K;
static u64 lv[64];

static void step(void) {
    u64 h = 10;
    for (int j = 0; j < K; j++) {
        u64 d = lv[j] + h;
        if (d & 1) {
            lv[j] = (d + 5) / 2;
            if (j + 1 < K) lv[j + 1] += (d - 1) / 2;
            return;
        }
        lv[j] = h = d / 2;
    }
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: bottom2adic K WARMUP PERIOD p_m p_(m-1) ...\n"); return 1; }
    K = atoi(argv[1]);
    u64 W = strtoull(argv[2], 0, 10), Q = strtoull(argv[3], 0, 10);
    if (K < 1 || K > 30 || argc < 4 + K) { fprintf(stderr, "need 1 <= K <= 30 and K blocks\n"); return 1; }
    for (int i = 0; i < K; i++) lv[i] = strtoull(argv[4 + i], 0, 10);
    for (u64 S = 0; S < W; S++) step();
    u64 st[64];
    for (int i = 0; i < K; i++) st[i] = lv[i];
    u64 M = 1ULL << K, *hist = calloc(M, sizeof(u64));
    for (u64 S = 0; S < Q; S++) {
        u64 N = 10;
        for (int i = 0; i < K; i++) N += lv[i] << i;
        hist[N & (M - 1)]++;
        step();
    }
    int same = 1;
    for (int i = 0; i < K; i++) same &= lv[i] == st[i];
    printf("# K=%d WARMUP=%llu PERIOD=%llu: the last K blocks %s after PERIOD\n", K, (unsigned long long)W,
           (unsigned long long)Q, same ? "come back" : "DO NOT come back (not a period)");
    for (int b = 1; b <= K; b++) {
        u64 Mb = 1ULL << b, H = Mb / 2, *hb = calloc(Mb, sizeof(u64)), zero = 0;
        for (u64 r = 0; r < M; r++) hb[r & (Mb - 1)] += hist[r];
        double dev = 0, mass = 0, lo = 1e18, hi = 0;
        for (u64 r = 1; r < H; r++) {
            u64 c = hb[r] + hb[r + H];
            if (!c) { zero++; continue; }
            dev += c * fabs((double)hb[r + H] / c - 0.5);
            mass += c;
        }
        for (u64 r = 1; r < Mb; r++) {
            double f = hb[r] * (double)Mb / Q;
            if (f < lo) lo = f;
            if (f > hi) hi = f;
        }
        if (mass > 0)
            printf("bit %2d  mean |P(1)-1/2| %.4f  unvisited classes mod 2^%d: %llu  nonzero residues mod 2^%d: "
                   "min %.3f max %.3f of uniform\n", b - 1, dev / mass, b - 1, (unsigned long long)zero, b, lo, hi);
        free(hb);
    }
    for (int j = 0; j < K; j++) {
        u64 c = 0;
        for (u64 r = 1; r < M; r++) if (__builtin_ctzll(r) == j) c += hist[r];
        printf("v2(N) = %2d: %.4f of 2^-(j+1)\n", j, c / (double)Q * (double)(2ULL << j));
    }
    printf("v2(N) >= %d: %.4f of 2^-%d\n", K, hist[0] / (double)Q * (double)M, K);
    u64 never = 0;
    for (u64 r = 0; r < M; r++) never += !hist[r];
    printf("residues mod 2^%d that never occur: %llu\n", K, (unsigned long long)never);
    for (int b = 1; b <= K && never; b++) {     /* the smallest modulus with a residue that never occurs */
        u64 Mb = 1ULL << b, *hb = calloc(Mb, sizeof(u64)), found = 0;
        for (u64 r = 0; r < M; r++) hb[r & (Mb - 1)] += hist[r];
        for (u64 r = 0; r < Mb; r++) {
            if (hb[r]) continue;
            found++;
            printf("never N = %llu mod 2^%d (binary ", (unsigned long long)r, b);
            for (int i = b - 1; i >= 0; i--) putchar('0' + (int)((r >> i) & 1));
            printf(")\n");
        }
        free(hb);
        if (found) {
            printf("these account for %llu of the %llu residues mod 2^%d that never occur\n",
                   (unsigned long long)(found << (K - b)), (unsigned long long)never, K);
            break;
        }
    }
    return 0;
}
