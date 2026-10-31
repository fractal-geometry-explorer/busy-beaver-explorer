/* passorbit.c: the closed-form pass map of 1RB1RA_1RC1LB_1LD0RA_1LB0LE_1LF1LD_---0LD (py/passmap.py, `passmap`),
 * iterated fast.  Trusted computation resting on the closed form, which is tested, not proved.
 *
 *   passorbit orbit N [Y1 Y2 ...]      N passes from the list (default [2, 2], the pass start at step 17); stops at
 *                                      the event.  Prints checkpoints at 10^m passes and every 10^9 (the list and a
 *                                      hash of every list so far, which py/passorbit.py recomputes) and the
 *                                      statistics of the run
 *   passorbit comps S0 S1 P  PART NPARTS
 *                                      every block list with S0 <= sum <= S1 (blocks >= 1), run P passes or to the
 *                                      event; parts.h protocol
 *   passorbit grid A B P  PART NPARTS  every two-block start [a, b], a <= A, b <= B, run P passes or to the event
 *   passorbit random R KMAX B P SEED  PART NPARTS
 *                                      R random lists (part PART draws items PART, PART + NPARTS, ... of the
 *                                      stream), 1 to KMAX blocks, each uniform in 1..B, run P passes or to the event
 *
 * PASSORBIT_EVENTS=N in the environment prints up to N `event` lines per part (default 200).
 *
 * The event: a sweep that stops at a block of a single 1 (outside the closed form), or a halt (the sweep runs off the
 * left end: last block odd, all others even).  Blocks are 64-bit; a pass adds 4 ones, so they cannot overflow here.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../../tools/c/parts.h"

#define MAXK 60
typedef uint64_t u64;

enum { OK = 0, HALT = 1, ONE = 2, BIG = 3 };
static const char *EVNAME[] = {"ok", "halt", "stop_block_1", "too_many_blocks"};

/* One pass on y[0..*k-1] in place.  Returns OK, HALT, ONE (stop block 1; y unchanged) or BIG (y unchanged).
 * *jout gets the 1-based stop index (0 for a halt), *stop the stop block when 1 <= j < k (else 0). */
static int pass(u64 *y, int *k, int *jout, u64 *stop) {
    int K = *k;
    int j;
    if (y[K - 1] % 2 == 0) j = K;
    else {
        j = K - 1;
        while (j >= 1 && y[j - 1] % 2 == 0) j--;
    }
    *jout = j;
    *stop = (j >= 1 && j < K) ? y[j - 1] : 0;
    if (j == 0) return HALT;
    u64 g[MAXK + 4], out[MAXK + 4];   /* g[i + 1] = Y(i), i = -1 .. K: the blank on the left is two empty blocks */
    g[0] = g[1] = 0;
    memcpy(g + 2, y, K * sizeof(u64));
#define Y(i) g[(i) + 1]
    int n = 0;
    if (j == K) {
        u64 add = y[K - 1] / 2 + 2;
        for (int i = -1; i <= K - 3; i++) out[n++] = Y(i);
        out[n++] = Y(K - 2) + add;
        out[n++] = Y(K - 1) + add;
    } else {
        u64 yj = Y(j);
        if (yj == 1) return ONE;
        u64 h[MAXK + 4];
        for (int i = j + 1; i < K; i++) h[i] = Y(i) / 2;
        h[K] = (y[K - 1] + 5) / 2;
        for (int i = -1; i <= j - 3; i++) out[n++] = Y(i);
        out[n++] = Y(j - 2) + (yj - 1) / 2;
        out[n++] = Y(j - 1) + (yj + 1) / 2 + h[j + 1];
        for (int i = j + 1; i < K; i++) out[n++] = h[i] + h[i + 1];
        out[n++] = h[K] - 1;
    }
#undef Y
    int s = 0;
    while (s < n && out[s] == 0) s++;
    if (n - s > MAXK) return BIG;
    *k = n - s;
    memcpy(y, out + s, (n - s) * sizeof(u64));
    return OK;
}

static void put_list(const u64 *y, int k) {
    putchar('[');
    for (int i = 0; i < k; i++) printf(i ? ", %llu" : "%llu", (unsigned long long)y[i]);
    putchar(']');
}

static void sput_list(char *buf, size_t len, const u64 *y, int k) {
    size_t p = snprintf(buf, len, "[");
    for (int i = 0; i < k && p < len; i++) p += snprintf(buf + p, len - p, i ? ",%llu" : "%llu", (unsigned long long)y[i]);
    if (p < len) snprintf(buf + p, len - p, "]");
}

/* A hash of the run: FNV-1a taken a 64-bit word at a time, over the blocks of each list and then 2^64 - 1. */
static u64 fnv(u64 h, const u64 *y, int k) {
    for (int i = 0; i < k; i++) h = (h ^ y[i]) * 1099511628211ULL;
    return (h ^ ~(u64)0) * 1099511628211ULL;
}

static int run_orbit(int argc, char **argv) {
    u64 N = strtoull(argv[2], 0, 10);
    u64 y[MAXK + 4];
    int k = 0;
    for (int i = 3; i < argc && k < MAXK; i++) y[k++] = strtoull(argv[i], 0, 10);
    if (!k) { y[0] = 2; y[1] = 2; k = 2; }
    u64 sum0 = 0;
    for (int i = 0; i < k; i++) sum0 += y[i];
    u64 hash = 14695981039346656037ULL, kc[MAXK + 1] = {0}, dc[7] = {0}, dother = 0, jfirst = 0, jlast = 0, jmid = 0;
    u64 min_stop = ~(u64)0, min_stop_at = 0, min_stop_sum = 0;
    u64 min_first = ~(u64)0, min_first_at = 0;          /* smallest first block over passes >= 50 */
    double min_ratio = 2; u64 min_ratio_at = 0, min_ratio_v = 0;
    u64 next_cp = 1, n, sum = sum0;
    int maxk = 0, ev = OK;
    for (n = 0; n < N; n++) {
        hash = fnv(hash, y, k);
        if (n + 1 == next_cp || (n + 1) % 1000000000ULL == 0 || n + 1 == N) {
            printf("checkpoint %llu ", (unsigned long long)(n + 1)); put_list(y, k);
            printf(" hash %016llx\n", (unsigned long long)hash);
            fflush(stdout);
            if (n + 1 == next_cp) next_cp *= 10;
        }
        kc[k]++;
        if (k > maxk) maxk = k;
        if (k == 2) {
            long long d = (long long)y[1] - 2 * (long long)y[0];
            if (d >= -3 && d <= 3) dc[d + 3]++; else dother++;
        }
        if (n >= 50 && y[0] < min_first) { min_first = y[0]; min_first_at = n; }
        int j, K = k; u64 stop;
        int r = pass(y, &k, &j, &stop);
        if (j == K) jlast++; else if (j == 1) jfirst++; else if (j > 1) jmid++;
        if (stop && n >= 50) {
            if (stop < min_stop) { min_stop = stop; min_stop_at = n; min_stop_sum = sum; }
            double q = (double)stop / (double)sum;
            if (q < min_ratio) { min_ratio = q; min_ratio_at = n; min_ratio_v = stop; }
        }
        if (r != OK) {
            ev = r;
            printf("event %s at pass %llu (0-based) list ", EVNAME[r], (unsigned long long)n);
            put_list(y, k); putchar('\n');
            break;
        }
        sum += 4;
    }
    printf("passes %llu event %s sum_at_end %llu blocks_at_end %d\n", (unsigned long long)n, EVNAME[ev],
           (unsigned long long)sum, k);
    printf("block_counts");
    for (int i = 1; i <= maxk; i++) if (kc[i]) printf(" %d:%llu", i, (unsigned long long)kc[i]);
    printf("\ntwo_block_d");
    for (int d = -3; d <= 3; d++) printf(" %d:%llu", d, (unsigned long long)dc[d + 3]);
    printf(" other:%llu\n", (unsigned long long)dother);
    printf("stops at_last_block %llu at_first_block %llu between %llu\n", (unsigned long long)jlast,
           (unsigned long long)jfirst, (unsigned long long)jmid);
    printf("min_stop_after_50 %llu at_pass %llu sum %llu\n", (unsigned long long)min_stop,
           (unsigned long long)min_stop_at, (unsigned long long)min_stop_sum);
    printf("min_stop_over_sum_after_50 %.6g at_pass %llu stop %llu\n", min_ratio, (unsigned long long)min_ratio_at,
           (unsigned long long)min_ratio_v);
    printf("min_first_block_after_50 %llu at_pass %llu\n", (unsigned long long)min_first,
           (unsigned long long)min_first_at);
    return 0;
}

/* Run one start for at most P passes.  Returns the event (OK if none) and the pass of it in *at. */
static int run_one(u64 *y, int *k, u64 P, u64 *at) {
    for (u64 n = 0; n < P; n++) {
        int j; u64 stop;
        int r = pass(y, k, &j, &stop);
        if (r != OK) { *at = n; return r; }
    }
    *at = P;
    return OK;
}

/* Per part: counts by event and by the start's sum mod 4 (a pass adds 4 ones, so it is kept until the event), when
 * the events came (by powers of two), the smallest start and the latest event of each kind with a witness. */
static u64 cnt[4][4], at_log[4][64], printed, minsum[4], latest[4];
static char minsum_w[4][512], latest_w[4][512];
static int seen[4];
static u64 max_printed = 200;     /* PASSORBIT_EVENTS=N in the environment prints up to N event lines per part */

static void record(const u64 *y0, int k0, int r, u64 at) {
    u64 sum0 = 0;
    for (int i = 0; i < k0; i++) sum0 += y0[i];
    cnt[r][sum0 % 4]++;
    if (r == OK) return;
    int b = 0;
    while ((2ULL << b) <= at + 1) b++;
    at_log[r][b]++;
    char s0[512];
    sput_list(s0, sizeof s0, y0, k0);
    if (!seen[r] || sum0 < minsum[r]) { minsum[r] = sum0; snprintf(minsum_w[r], 512, "%s", s0); }
    if (!seen[r] || at > latest[r]) { latest[r] = at; snprintf(latest_w[r], 512, "%s", s0); }
    seen[r] = 1;
    if (printed < max_printed) { parts_event("%s start %s pass %llu", EVNAME[r], s0, (unsigned long long)at); printed++; }
}

static void report(void) {
    char nm[64];
    for (int r = 0; r < 4; r++) {
        for (int m = 0; m < 4; m++) {
            snprintf(nm, sizeof nm, "%s_sum_mod4_%d", r == OK ? "no_event" : EVNAME[r], m);
            parts_sum(nm, (long long)cnt[r][m]);
        }
        if (r == OK || !seen[r]) continue;
        for (int b = 0; b < 64; b++)
            if (at_log[r][b]) { snprintf(nm, sizeof nm, "%s_at_pass_lt_2^%d", EVNAME[r], b + 1); parts_sum(nm, (long long)at_log[r][b]); }
        snprintf(nm, sizeof nm, "%s_smallest_start_sum", EVNAME[r]);
        parts_min(nm, (long long)minsum[r], "%s", minsum_w[r]);
        snprintf(nm, sizeof nm, "%s_latest_pass", EVNAME[r]);
        parts_max(nm, (long long)latest[r], "%s", latest_w[r]);
    }
    parts_done();
}

/* Compositions of S: bit i of c (i < S-1) set means a cut after cell i. */
static int run_comps(int argc, char **argv) {
    parts_args(argc, argv, 5);
    int S0 = atoi(argv[2]), S1 = atoi(argv[3]);
    u64 P = strtoull(argv[4], 0, 10);
    u64 item = 0;
    for (int S = S0; S <= S1; S++) {
        for (u64 c = 0; c < (1ULL << (S - 1)); c++, item++) {
            if (!parts_owns(item)) continue;
            u64 y0[MAXK + 4], y[MAXK + 4];
            int k = 0;
            u64 len = 1;
            for (int i = 0; i < S - 1; i++) {
                if (c >> i & 1) { y0[k++] = len; len = 1; } else len++;
            }
            y0[k++] = len;
            if (k > MAXK) continue;
            memcpy(y, y0, k * sizeof(u64));
            int kk = k;
            u64 at;
            int r = run_one(y, &kk, P, &at);
            record(y0, k, r, at);
        }
    }
    report();
    return 0;
}

/* splitmix64, seeded per item so a split into parts draws the same lists */
static u64 mix(u64 x) {
    x += 0x9e3779b97f4a7c15ULL;
    x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
    x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
    return x ^ (x >> 31);
}

static int run_random(int argc, char **argv) {
    parts_args(argc, argv, 7);
    u64 R = strtoull(argv[2], 0, 10);
    int KM = atoi(argv[3]);
    u64 B = strtoull(argv[4], 0, 10), P = strtoull(argv[5], 0, 10), seed = strtoull(argv[6], 0, 10);
    if (KM < 1 || KM > MAXK) { fprintf(stderr, "KMAX out of range\n"); return 1; }
    for (u64 i = 0; i < R; i++) {
        if (!parts_owns(i)) continue;
        u64 st = mix(seed * 0x100000001b3ULL + i), y0[MAXK + 4], y[MAXK + 4];
        int k = 1 + (int)((st = mix(st)) % (u64)KM);
        for (int t = 0; t < k; t++) y0[t] = 1 + (st = mix(st)) % B;
        memcpy(y, y0, k * sizeof(u64));
        int kk = k;
        u64 at;
        int r = run_one(y, &kk, P, &at);
        record(y0, k, r, at);
    }
    report();
    return 0;
}

/* every start [a, b], 1 <= a <= A, 1 <= b <= B */
static int run_grid(int argc, char **argv) {
    parts_args(argc, argv, 5);
    u64 A = strtoull(argv[2], 0, 10), B = strtoull(argv[3], 0, 10), P = strtoull(argv[4], 0, 10);
    for (u64 a = 1; a <= A; a++) {
        if (!parts_owns(a)) continue;
        for (u64 b = 1; b <= B; b++) {
            u64 y0[2] = {a, b}, y[MAXK + 4] = {a, b}, at;
            int k = 2;
            int r = run_one(y, &k, P, &at);
            record(y0, 2, r, at);
        }
    }
    report();
    return 0;
}

int main(int argc, char **argv) {
    if (getenv("PASSORBIT_EVENTS")) max_printed = strtoull(getenv("PASSORBIT_EVENTS"), 0, 10);
    if (argc >= 3 && !strcmp(argv[1], "orbit")) return run_orbit(argc, argv);
    if (argc >= 5 && !strcmp(argv[1], "comps")) return run_comps(argc, argv);
    if (argc >= 7 && !strcmp(argv[1], "random")) return run_random(argc, argv);
    if (argc >= 5 && !strcmp(argv[1], "grid")) return run_grid(argc, argv);
    fprintf(stderr, "usage: see the comment at the top of passorbit.c\n");
    return 1;
}
