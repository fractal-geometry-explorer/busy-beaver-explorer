/* Sweep starts of 1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA (bbchallenge 15414).
   lean/Sweep.lean (halts_iff_sweep): the machine halts iff some frame starts a halting sweep. At a B frame with
   right list r0, r1, r2, ... that means r0 = 3 and r1 >= 1, or r0 != 2 and the first of r1, r2, ... below 2 is
   a 1 followed by a non-empty block. This runs the block map with zigzags in one step (as c/series.c) and, at
   every B frame, tests that condition and records how close the list comes to it:
     - r0 when it is small (r0 < 32) and not the last block,
     - the smallest block among r1, r2, ... that the sweep reads before turning, when it is not the last block.
   usage: ./sweeps MAXFRAMES */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef int64_t i64;
#define CAP 4096
static i64 L[CAP], R[CAP]; static int lp, rp, q;
#define POPL() (lp ? L[--lp] : 0)
#define POPR() (rp ? R[--rp] : 0)
#define PUSHL(x) (L[lp++] = (x))
#define PUSHR(x) (R[rp++] = (x))
static uint64_t r0h[32], minh[32], nb, nbad, nturn;
static void at_B(uint64_t n) {
    nb++;
    if (rp == 0) return;                     /* blank on the right: C (0 :: ...) [] turns round */
    i64 r0 = R[rp - 1];
    int last = rp == 1;
    if (r0 == 2) { nturn++; return; }
    if (!last && r0 < 32) r0h[r0]++;
    if (r0 == 3) { if (!last && R[rp - 2] >= 1) { nbad++; printf("BAD (r0 = 3) at frame %llu\n", (unsigned long long)n); } return; }
    i64 mn = -1;
    for (int k = rp - 2; k >= 0; k--) {      /* r1, r2, ... */
        i64 v = R[k];
        if (k > 0 && (mn < 0 || v < mn)) mn = v;
        if (v <= 1) {
            if (v == 1 && k > 0 && R[k - 1] >= 1) { nbad++; printf("BAD (interior 1) at frame %llu\n", (unsigned long long)n); }
            break;
        }
    }
    if (mn >= 0) minh[mn < 31 ? mn : 31]++;
}
int main(int argc, char **argv) {
    uint64_t maxn = strtoull(argv[1], 0, 10), n = 0;
    q = 2; PUSHL(1);
    while (n < maxn) {
        if (lp > CAP - 8 || rp > CAP - 8) { printf("too many blocks\n"); return 1; }
        if (q == 2 && n > 0) at_B(n);
        if (q == 0) {
            i64 i = POPL(), m = POPR();
            if (m == 0) { PUSHR(i + 1); }
            else if (m == 1) { i64 r = POPR(); PUSHL(i + 2); PUSHL(r); q = 1; }
            else if (m >= 5 && rp >= 2 && R[rp - 1] == 0) { i64 t = (m - 2) / 3; R[rp - 2] += t; PUSHR(m - 3 * t); PUSHL(i + 2 * t); }
            else { PUSHL(i + 2); PUSHL(m - 2); q = 1; }
        } else if (q == 1) {
            i64 a = POPL(), r = POPR();
            if (a == 0) { PUSHL(r + 1); }
            else if (a == 1) { i64 b = POPL(); PUSHR(r + 1); PUSHR(0); PUSHR(b); q = 0; }
            else if (a == 2) { if (r >= 1) { printf("CRITICAL FRAME at %llu\n", (unsigned long long)n); break; } i64 b = POPL(); PUSHL(b + 5); q = 2; }
            else { PUSHL(a - 1); PUSHL(r + 1); }
        } else if (q == 2) {
            i64 a = POPL(), r = POPR();
            if (r == 0) { i64 s = POPR(); PUSHL(a); PUSHL(s); q = 1; }
            else if (a <= 1) { printf("B frame with a <= 1 (Invariant.lean says impossible)\n"); return 1; }
            else { PUSHL(a); PUSHL(r - 1); q = 1; }
        } else { printf("F frame (Invariant.lean says impossible)\n"); return 1; }
        n++;
    }
    i64 w = 0; for (int k = 0; k < lp; k++) w += L[k]; for (int k = 0; k < rp; k++) w += R[k];
    printf("%llu frames, %llu B frames (%llu turn at once), halting sweep starts: %llu, ones at the end: %lld\n",
           (unsigned long long)n, (unsigned long long)nb, (unsigned long long)nturn, (unsigned long long)nbad, (long long)w);
    printf("r0 (first block right of B, not the last block), values below 32:");
    for (int k = 0; k < 32; k++) if (r0h[k]) printf(" %d:%llu", k, (unsigned long long)r0h[k]);
    printf("\nsmallest later block the sweep reads (not the last block), values below 31 (31 = 31 or more):");
    for (int k = 0; k < 32; k++) if (minh[k]) printf(" %d:%llu", k, (unsigned long long)minh[k]);
    printf("\n");
    return 0;
}
