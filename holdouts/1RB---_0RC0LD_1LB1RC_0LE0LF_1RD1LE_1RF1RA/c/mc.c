/* Series-level run of the block map of 1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA (bbchallenge 15414).
   The map is `next` of lean/Blocks.lean (py/blockmap.py), with one shortcut: a zigzag
   E (i::L) (m::0::j::R), m >= 5, is t = (m-2)/3 trips at once: E (i+2t::L) (m-3t::0::j+t::R).
   Halts are detected exactly (the three critical frames); a fixed frame is reported as a loop.
   This file: the same step function as series.c. Not the usage below: ./series MAXFRAMES [checkpoint-file]   (resumes from the checkpoint if it exists) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
typedef int64_t i64;
#define CAP 4096
static i64 L[CAP], R[CAP]; static int lp, rp; static int q; /* 0=E 1=C 2=B 3=F */
static uint64_t n;
#ifdef STATS
static uint64_t hist[32], oct[80];
#endif
#define POPL() (lp ? L[--lp] : 0)
#define POPR() (rp ? R[--rp] : 0)
#define PUSHL(x) (L[lp++] = (x))
#define PUSHR(x) (R[rp++] = (x))

static int step(void) {
        if (q == 0) {
            i64 i = POPL(), m = POPR();
#ifdef STATS
            if (lp == 0 && i == 0 && m >= 2 && rp >= 1 && R[rp - 1] == 0 && m <= 20) {
                i64 w = 0; for (int k = 0; k < rp; k++) w += R[k]; w += m;
                int o = 0; while (w > 1) { w >>= 1; o++; }
                hist[m]++; oct[o]++;
            }
#endif
            if (m == 0) { PUSHR(i + 1); }
            else if (m == 1) { i64 r = POPR(); PUSHL(i + 2); PUSHL(r); q = 1; }
            else if (m >= 5 && rp >= 2 && R[rp - 1] == 0) {
                i64 t = (m - 2) / 3;
                R[rp - 2] += t; PUSHR(m - 3 * t); PUSHL(i + 2 * t);
            } else {
                if (m == 2 && i == 0 && lp == 0 && rp >= 1 && R[rp - 1] == 0) { PUSHR(m); return 2; }
                PUSHL(i + 2); PUSHL(m - 2); q = 1;
            }
        } else if (q == 1) {
            i64 a = POPL(), r = POPR();
            if (a == 0) { PUSHL(r + 1); }
            else if (a == 1) { i64 b = POPL(); PUSHR(r + 1); PUSHR(0); PUSHR(b); q = 0; }
            else if (a == 2) { if (r >= 1) { PUSHR(r); PUSHL(a); return 1; } i64 b = POPL(); PUSHL(b + 5); q = 2; }
            else { PUSHL(a - 1); PUSHL(r + 1); }
        } else if (q == 2) {
            i64 a = POPL(), r = POPR();
            if (r == 0) { i64 s = POPR(); PUSHL(a); PUSHL(s); q = 1; }
            else if (a == 0) { i64 b = POPL(); PUSHR(r - 1); PUSHR(0); PUSHR(b); q = 0; }
            else if (a == 1) {
                i64 b = POPL();
                if (r == 1) { PUSHL(b + 4); q = 3; }
                else if (r == 2) { PUSHL(b + 5); }
                else { PUSHL(b); PUSHL(a); PUSHR(r); return 1; }
            } else { PUSHL(a); PUSHL(r - 1); q = 1; }
        } else {
            i64 a = POPL(), r = POPR();
            if (r == 0) { PUSHL(a + 1); }
            else if (r == 1) { PUSHL(a + 2); q = 2; }
            else { PUSHL(a); PUSHR(r); return 1; }
        }
        return 0;
}
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
/* Randomized restarts for 15414: run the block map from blank tape to FRAMES frames, then TRIALS times: add a random
   0..SPREAD-1 to every block of at least SPREAD cells and run until the number of ones has grown GROW-fold (or a
   critical frame / the left-end loop is met).  usage: ./mc FRAMES TRIALS SPREAD GROW [seed] */
int main(int argc, char **argv) {
    uint64_t frames = strtoull(argv[1], 0, 10); long trials = atol(argv[2]); i64 spread = atoll(argv[3]); int grow = atoi(argv[4]);
    if (argc > 5) rs ^= strtoull(argv[5], 0, 10) * 0x9E3779B97F4A7C15ULL;
    q = 2; lp = 0; rp = 0; PUSHL(1);
    for (n = 0; n < frames; n++) if (step()) { printf("ended before start\n"); return 1; }
    static i64 L0[CAP], R0[CAP]; int lp0 = lp, rp0 = rp, q0 = q;
    memcpy(L0, L, sizeof L); memcpy(R0, R, sizeof R);
    i64 w0 = 0; for (int k = 0; k < lp; k++) w0 += L[k]; for (int k = 0; k < rp; k++) w0 += R[k];
    long halts = 0, loops = 0, ok = 0; uint64_t tot = 0;
    for (long t = 0; t < trials; t++) {
        memcpy(L, L0, sizeof L); memcpy(R, R0, sizeof R); lp = lp0; rp = rp0; q = q0;
        for (int k = 0; k < lp; k++) if (L[k] >= spread) L[k] += rnd() % spread;
        for (int k = 0; k < rp; k++) if (R[k] >= spread) R[k] += rnd() % spread;
        int st = 0; uint64_t c = 0;
        while (1) {
            st = step(); c++;
            if (st) break;
            if ((c & 1023) == 0) { i64 w = 0; for (int k = 0; k < lp; k++) w += L[k]; for (int k = 0; k < rp; k++) w += R[k]; if (w >= w0 * grow) break; }
        }
        tot += c;
        if (st == 1) halts++; else if (st == 2) loops++; else ok++;
    }
    printf("start: %llu frames, %lld ones; %ld trials, spread %lld, grow x%d: %ld reach a critical frame, %ld reach the left-end loop, %ld neither (%llu frames in all)\n",
           (unsigned long long)frames, (long long)w0, trials, (long long)spread, grow, halts, loops, ok, (unsigned long long)tot);
    return 0;
}
