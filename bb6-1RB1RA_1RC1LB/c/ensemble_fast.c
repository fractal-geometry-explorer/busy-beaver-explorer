/* ensemble_fast: c/ensemble.c on the periodic tables of c/superrun.c, with the statistics of the returns kept in C.
 *
 *   ensemble_fast [-v] [-u] ORBITS SUPER_STEPS SEED MIN_BLOCKS MAX_BLOCKS MAX_BLOCK FIRST_ID
 *
 * The starts are those of c/ensemble.c with the same arguments (the same xorshift64 and the same order of draws), and
 * the returns are the same: each orbit runs the super step from [p_1, ..., p_m, 5, 0] for SUPER_STEPS super steps,
 * the bottom levels tabulated as soon as they cycle (the method of c/superrun.c, without the machine step counts), so
 * an orbit of 2^24 super steps takes about 2 ms instead of 65.  An orbit stops early when a tabulated level only
 * receives adds (the bottom has gone silent, lean/Cycles.lean: for example a last block of 15, as 15 + 10 = 25 turns
 * back into 15), since it has no more returns.  Unlike c/superrun.c, a level is tabulated even when only the top
 * level would be left explicit, so that such orbits are caught however few blocks they have.  Blocks are 128-bit (an orbit whose value would pass
 * 2^126, or whose table value would pass 2^62, is dropped and counted, as c/ensemble.c drops one past 2^62).
 *
 * -u counts each return once over the whole run: a return whose d1, number of blocks m and the (up to) three blocks
 * below the top all equal those of an earlier return (of any orbit) is skipped in the totals, as the two orbits have
 * almost surely merged (counted as "dups").  Narrow starts repeat and merge often (2 blocks of 1..100 have only 10^4
 * tapes), so without -u their returns are far from independent.
 *
 * -v prints the lines of c/ensemble.c ("start ID p_1,...,p_m" and "R ID S m d1 H", m the blocks before the return),
 * for tests/test_top.py.  Without -v it prints only the totals:
 *   "orbits N dropped D returns R halts H dups X"
 *   "cell b s n"   n returns with d1 of b bits (2^(b-1) <= d1 < 2^b) and v2(d1) = s
 *   "inv b x"      the sum of 1/d1 over the returns with d1 of b bits (%.17Le)
 *   "rcell k b s n" the same, for the k-th return of an orbit only (k from 1, capped at 64)
 *   "pair a c n"   n pairs of consecutive returns of one orbit with v2 = a, then v2 = c (a, c capped at 15), both
 *                  with d1 >= 2^12
 * py/top_stats.py `fast` reads and adds up these files.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef uint64_t u64;
typedef unsigned __int128 u128;

static u64 rs;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

/* ---- the table of the bottom K levels: each entry is dt super steps, then an add (top bit) or a wave of v ---- */
typedef struct { u64 dt, v; } ent;
#define ADDBIT (1ull << 63)
static ent *tab;
static u64 ntab, tail_dt;
static int K;

#define MAXL 4096
static u128 up[MAXL];
static int nup;
static u128 S;
static int bad;             /* the orbit is dropped */
static int halted;
static int verbose, uniq;
static u64 ndup, *seen, seen_mask;
static long cur_id;

#define MB 130
static u64 cell[MB][MB], pairs[16][16], rcell[65][MB][MB];
static int ret_k;            /* returns of this orbit so far */
static long double inv[MB];
static u64 nret, nhalt;
static int prev_s;          /* v2 of the previous return of this orbit with d1 >= 2^12, or -1 */

static int bits128(u128 v) { int b = 0; while (v) { b++; v >>= 1; } return b; }

static void u128_str(u128 v, char *out) {
    char buf[48];
    int k = 47;
    buf[k] = 0;
    do { buf[--k] = (char)('0' + (int)(v % 10)); v /= 10; } while (v);
    strcpy(out, buf + k);
}

static int build(u64 p0, int L) {
    u64 nw = 0;
    for (u64 i = 0; i < ntab; i++) nw += !(tab[i].v & ADDBIT);
    if (!nw || nw * L > 50000000) return 0;
    ent *nt = malloc(sizeof(ent) * nw * L);
    if (!nt) return 0;
    u64 p = p0, n = 0, adt = 0;
    for (int pass = 0; pass < L; pass++) {
        for (u64 i = 0; i < ntab; i++) {
            const ent *e = &tab[i];
            adt += e->dt;
            if (e->v & ADDBIT) { p += e->v & ~ADDBIT; continue; }
            u64 d = p + e->v;
            if (d >> 62) { free(nt); return 0; }   /* too big for the table: stay explicit */
            ent *o = &nt[n++];
            o->dt = adt;
            if (d & 1) { o->v = ((d - 1) >> 1) | ADDBIT; p = (d + 5) >> 1; }
            else { o->v = d >> 1; p = d >> 1; }
            adt = 0;
        }
        adt += tail_dt;
        if (adt >> 62) { free(nt); return 0; }
    }
    if (p != p0) { free(nt); return 0; }
    free(tab);
    tab = nt; ntab = n; tail_dt = adt;
    K++;
    for (u64 i = 0; i < ntab; i++) if (!(tab[i].v & ADDBIT)) return 1;
    return 2;   /* level K only ever receives adds: nothing passes it again, so no more returns (a silent bottom) */
}

static void left_end(u128 d1) {
    int s = 0;
    u128 u = d1;
    while (!(u & 1)) { u >>= 1; s++; }
    int b = bits128(d1);
    if (verbose) {
        char ss[48], ds[48];
        u128_str(S, ss); u128_str(d1, ds);
        printf("R %ld %s %d %s %d\n", cur_id, ss, K + nup, ds, u == 1);
    }
    if (uniq) {
        u64 h = (u64)d1 * 0x9E3779B97F4A7C15ull ^ (u64)(d1 >> 64) * 0xC2B2AE3D27D4EB4Full ^ (u64)(K + nup);
        for (int i = 2; i <= 4 && i <= nup; i++) {
            h ^= (u64)up[nup - i] + 0x165667B19E3779F9ull + (h << 6) + (h >> 2);
            h ^= (u64)(up[nup - i] >> 64) * 0x27D4EB2F165667C5ull;
        }
        h = h * 0xFF51AFD7ED558CCDull; h ^= h >> 33; h = h * 0xC4CEB9FE1A85EC53ull; h ^= h >> 33;
        if (!h) h = 1;
        u64 i = h & seen_mask;
        while (seen[i] && seen[i] != h) i = (i + 1) & seen_mask;
        if (seen[i]) { ndup++; goto after; }
        seen[i] = h;
    }
    nret++;
    cell[b][s]++;
    ret_k += ret_k < 64;
    rcell[ret_k][b][s]++;
    inv[b] += 1.0L / (long double)d1;
    if (b >= 13) {
        int a = s > 15 ? 15 : s;
        if (prev_s >= 0) pairs[prev_s][a]++;
        prev_s = a;
    }
    if (u == 1) nhalt++;
after:
    if (u == 1) { halted = 1; return; }
    nup--;
    if (nup + s + 2 >= MAXL || bits128(u) + s > 125) { bad = 1; return; }
    for (int t = s - 1; t >= 0; t--) up[nup++] = u << t;
    up[nup++] = (u + 5) >> 1;
    up[nup++] = (u - 1) >> 1;
}

static void wave(u128 h) {
    for (int k = 0;; k++) {
        u128 d = up[k] + h;
        if (d >> 126) { bad = 1; return; }
        if (k == nup - 1) { left_end(d); return; }
        if (d & 1) { up[k] = (d + 5) >> 1; up[k + 1] += (d - 1) >> 1; return; }
        up[k] = d >> 1;
        h = d >> 1;
    }
}

static void run(u128 budget) {
    free(tab);
    tab = malloc(sizeof(ent));
    tab[0].dt = 1; tab[0].v = 10;
    ntab = 1; tail_dt = 0; K = 0;
    S = 0; bad = 0; halted = 0; prev_s = -1; ret_k = 0;
    u128 hist[256];
    u64 wraps = 0;
    for (;;) {
        for (u64 i = 0; i < ntab; i++) {
            const ent *e = &tab[i];
            S += e->dt;
            if (S > budget) return;
            if (e->v & ADDBIT) up[0] += e->v & ~ADDBIT;
            else {
                wave(e->v);
                if (bad || halted) return;
            }
        }
        S += tail_dt;
        if (S >= budget) return;
        int found = 0;
        if (nup >= 2 && up[0] < ((u128)1 << 61)) {
            for (u64 L = 1; L <= 256 && L <= wraps; L++)
                if (hist[(wraps - L) % 256] == up[0]) {
                    int r = build((u64)up[0], (int)L);
                    if (r == 2) return;
                    if (r) {
                        memmove(up, up + 1, sizeof(u128) * (nup - 1));
                        nup--;
                        found = 1;
                    }
                    break;
                }
        }
        if (found) wraps = 0;
        else { hist[wraps % 256] = up[0]; wraps++; }
    }
}

int main(int argc, char **argv) {
    int a = 1;
    for (; a < argc && argv[a][0] == '-' && argv[a][1] && !argv[a][2]; a++) {
        if (argv[a][1] == 'v') verbose = 1;
        else if (argv[a][1] == 'u') uniq = 1;
        else break;
    }
    if (argc - a < 7) {
        fprintf(stderr, "usage: ensemble_fast [-v] [-u] ORBITS SUPER_STEPS SEED MIN_BLOCKS MAX_BLOCKS MAX_BLOCK FIRST_ID\n");
        return 1;
    }
    long n = atol(argv[a]), id0 = atol(argv[a + 6]);
    u128 budget = (u128)strtold(argv[a + 1], 0);
    u64 vmax = strtoull(argv[a + 5], 0, 10);
    int lo = atoi(argv[a + 3]), hi = atoi(argv[a + 4]);
    rs = strtoull(argv[a + 2], 0, 10) * 2654435761ULL + 12345;
    u64 dropped = 0;
    if (uniq) {
        u64 n2 = 1;
        while (n2 < (u64)n * 40) n2 <<= 1;        /* about 10 returns per orbit: the table stays at most 1/4 full */
        seen = calloc(n2, sizeof(u64));
        if (!seen) { fprintf(stderr, "ensemble_fast: no memory for -u\n"); return 1; }
        seen_mask = n2 - 1;
    }
    for (long id = id0; id < id0 + n; id++) {
        int m = lo + (int)(rnd() % (u64)(hi - lo + 1));
        u64 P[MAXL];
        for (int i = m - 1; i >= 0; i--) P[i] = 1 + rnd() % vmax;   /* P[m-1] = p_1, ..., P[0] = p_m, as ensemble.c */
        if (verbose) {
            printf("start %ld ", id);
            for (int i = m - 1; i >= 0; i--) printf("%llu%s", (unsigned long long)P[i], i ? "," : "\n");
        }
        cur_id = id;
        for (nup = 0; nup < m; nup++) up[nup] = P[nup];       /* level 0 = p_m */
        run(budget);
        if (bad) { dropped++; if (verbose) printf("overflow %ld\n", id); }
    }
    if (verbose) return 0;
    printf("orbits %ld dropped %llu returns %llu halts %llu dups %llu\n", n, (unsigned long long)dropped,
           (unsigned long long)nret, (unsigned long long)nhalt, (unsigned long long)ndup);
    for (int b = 0; b < MB; b++) {
        for (int s = 0; s < MB; s++)
            if (cell[b][s]) printf("cell %d %d %llu\n", b, s, (unsigned long long)cell[b][s]);
        if (inv[b] > 0) printf("inv %d %.17Le\n", b, inv[b]);
    }
    for (int k = 1; k <= 64; k++)
        for (int b = 0; b < MB; b++)
            for (int t = 0; t < MB; t++)
                if (rcell[k][b][t]) printf("rcell %d %d %d %llu\n", k, b, t, (unsigned long long)rcell[k][b][t]);
    for (int x = 0; x < 16; x++)
        for (int y = 0; y < 16; y++)
            if (pairs[x][y]) printf("pair %d %d %llu\n", x, y, (unsigned long long)pairs[x][y]);
    return 0;
}
