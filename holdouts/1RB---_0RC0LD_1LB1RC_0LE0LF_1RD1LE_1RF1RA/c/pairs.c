/* How close the run of 1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA (bbchallenge 15414) comes to a pattern frame.
   lean/Pair.lean (halts_iff_pat): the machine halts iff the block map reaches E L (3 :: 0 :: j :: R) with
   hd L = 8, or with L = [3] (a leftmost block of 3).  This runs the block map with zigzags in one step (as
   c/series.c), so every frame E (i :: L) (3 :: 0 :: j :: R) the Lean map reaches is seen (the zigzag ends on it,
   or the block had 3 cells to begin with), and records the block i left of the head there:
     - a histogram of i below 64, split into "leftmost" (i is the leftmost block of the tape) and "inner",
     - the smallest i seen of each kind after the first 1000 frames, with the frame,
     - a pattern frame, if one occurs (then it stops: the machine halts).
   usage: ./pairs MAXFRAMES */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef int64_t i64;
#define CAP 8192
static i64 L[CAP], R[CAP]; static int lp, rp, q;
static uint64_t n;
#define POPL() (lp ? L[--lp] : 0)
#define POPR() (rp ? R[--rp] : 0)
#define PUSHL(x) (L[lp++] = (x))
#define PUSHR(x) (R[rp++] = (x))
static uint64_t hin[64], hlm[64], cnt;
static i64 minin = -1, minlm = -1; static uint64_t atin, atlm;
static void dump(void) {
    printf("frame %llu %c L (head first):", (unsigned long long)n, "ECBF"[q]);
    for (int k = lp - 1; k >= 0 && k >= lp - 8; k--) printf(" %lld", (long long)L[k]);
    printf(lp > 8 ? " ... R:" : " R:");
    for (int k = rp - 1; k >= 0 && k >= rp - 8; k--) printf(" %lld", (long long)R[k]);
    printf(rp > 8 ? " ...\n" : "\n");
}
int main(int argc, char **argv) {
    uint64_t maxn = strtoull(argv[1], 0, 10);
    q = 2; PUSHL(1);
    while (n < maxn) {
        if (lp > CAP - 8 || rp > CAP - 8) { printf("too many blocks\n"); return 1; }
        if (q == 0 && rp >= 3 && R[rp - 1] == 3 && R[rp - 2] == 0) {
            i64 i = lp ? L[lp - 1] : 0; int lm = lp <= 1;
            cnt++;
            if (i < 64) (lm ? hlm : hin)[i]++;
            if (n > 1000) {
                if (lm && (minlm < 0 || i < minlm)) { minlm = i; atlm = n; }
                if (!lm && (minin < 0 || i < minin)) { minin = i; atin = n; }
            }
            if (i == 8 || (i == 3 && lp == 1)) { printf("PATTERN FRAME (the machine halts): "); dump(); return 0; }
        }
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
            else if (a == 2) { if (r >= 1) { printf("CRITICAL FRAME without a pattern frame (contradicts Pair.lean)\n"); return 1; } i64 b = POPL(); PUSHL(b + 5); q = 2; }
            else { PUSHL(a - 1); PUSHL(r + 1); }
        } else if (q == 2) {
            i64 a = POPL(), r = POPR();
            if (r == 0) { i64 s = POPR(); PUSHL(a); PUSHL(s); q = 1; }
            else { PUSHL(a); PUSHL(r - 1); q = 1; }
        } else { printf("F frame\n"); return 1; }
        n++;
    }
    i64 w = 0; for (int k = 0; k < lp; k++) w += L[k]; for (int k = 0; k < rp; k++) w += R[k];
    printf("%llu frames, no pattern frame; %llu frames E (i :: L) (3 :: 0 :: j :: R); ones at the end: %lld\n",
           (unsigned long long)n, (unsigned long long)cnt, (long long)w);
    printf("i = leftmost block, i < 64:"); for (int k = 0; k < 64; k++) if (hlm[k]) printf(" %d:%llu", k, (unsigned long long)hlm[k]);
    printf("\ni = inner block, i < 64:"); for (int k = 0; k < 64; k++) if (hin[k]) printf(" %d:%llu", k, (unsigned long long)hin[k]);
    printf("\nsmallest i after frame 1000: leftmost %lld (frame %llu), inner %lld (frame %llu)\n",
           (long long)minlm, (unsigned long long)atlm, (long long)minin, (unsigned long long)atin);
    return 0;
}
