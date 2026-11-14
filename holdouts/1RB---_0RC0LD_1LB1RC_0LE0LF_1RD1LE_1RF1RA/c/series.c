/* Series-level run of the block map of 1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA (bbchallenge 15414).
   The map is `next` of lean/Blocks.lean (py/blockmap.py), with one shortcut: a zigzag
   E (i::L) (m::0::j::R), m >= 5, is t = (m-2)/3 trips at once: E (i+2t::L) (m-3t::0::j+t::R).
   Halts are detected exactly (the three critical frames); a fixed frame is reported as a loop.
   usage: ./series MAXFRAMES [checkpoint-file]   (resumes from the checkpoint if it exists) */
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
static void dump(FILE *f) {
    fprintf(f, "%llu %c L", (unsigned long long)n, "ECBF"[q]);
    for (int k = lp - 1; k >= 0; k--) fprintf(f, " %lld", (long long)L[k]);
    fprintf(f, " R");
    for (int k = rp - 1; k >= 0; k--) fprintf(f, " %lld", (long long)R[k]);
    fprintf(f, "\n");
}
static void save(const char *fn) {
    char tmp[1024]; snprintf(tmp, sizeof tmp, "%s.tmp", fn);
    FILE *f = fopen(tmp, "wb"); if (!f) return;
    fwrite(&n, 8, 1, f); fwrite(&q, 4, 1, f); fwrite(&lp, 4, 1, f); fwrite(&rp, 4, 1, f);
    fwrite(L, 8, lp, f); fwrite(R, 8, rp, f); fclose(f); rename(tmp, fn);
}
static int load(const char *fn) {
    FILE *f = fopen(fn, "rb"); if (!f) return 0;
    if (fread(&n, 8, 1, f) != 1) { fclose(f); return 0; }
    fread(&q, 4, 1, f); fread(&lp, 4, 1, f); fread(&rp, 4, 1, f);
    fread(L, 8, lp, f); fread(R, 8, rp, f); fclose(f); return 1;
}
int main(int argc, char **argv) {
    uint64_t maxn = strtoull(argv[1], 0, 10);
    const char *ck = argc > 2 ? argv[2] : 0;
    if (!(ck && load(ck))) { q = 2; lp = 0; rp = 0; PUSHL(1); n = 0; }   /* B [1] [] after one step */
    time_t last = time(0);
    int status = 0;
    while (n < maxn) {
        if (lp > CAP - 8 || rp > CAP - 8) { status = 3; break; }
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
                if (m == 2 && i == 0 && lp == 0 && rp >= 1 && R[rp - 1] == 0) { PUSHR(m); status = 2; break; }
                PUSHL(i + 2); PUSHL(m - 2); q = 1;
            }
        } else if (q == 1) {
            i64 a = POPL(), r = POPR();
            if (a == 0) { PUSHL(r + 1); }
            else if (a == 1) { i64 b = POPL(); PUSHR(r + 1); PUSHR(0); PUSHR(b); q = 0; }
            else if (a == 2) { if (r >= 1) { PUSHR(r); PUSHL(a); status = 1; break; } i64 b = POPL(); PUSHL(b + 5); q = 2; }
            else { PUSHL(a - 1); PUSHL(r + 1); }
        } else if (q == 2) {
            i64 a = POPL(), r = POPR();
            if (r == 0) { i64 s = POPR(); PUSHL(a); PUSHL(s); q = 1; }
            else if (a == 0) { i64 b = POPL(); PUSHR(r - 1); PUSHR(0); PUSHR(b); q = 0; }
            else if (a == 1) {
                i64 b = POPL();
                if (r == 1) { PUSHL(b + 4); q = 3; }
                else if (r == 2) { PUSHL(b + 5); }
                else { PUSHL(b); PUSHL(a); PUSHR(r); status = 1; break; }
            } else { PUSHL(a); PUSHL(r - 1); q = 1; }
        } else {
            i64 a = POPL(), r = POPR();
            if (r == 0) { PUSHL(a + 1); }
            else if (r == 1) { PUSHL(a + 2); q = 2; }
            else { PUSHL(a); PUSHR(r); status = 1; break; }
        }
        n++;
        if ((n & 0xfffffff) == 0) {
            time_t now = time(0);
            if (ck && now - last >= 600) {
                last = now; save(ck);
                i64 w = 0; for (int k = 0; k < lp; k++) w += L[k]; for (int k = 0; k < rp; k++) w += R[k];
                printf("frames %llu ones %lld blocks %d\n", (unsigned long long)n, (long long)w, lp + rp); fflush(stdout);
            }
        }
    }
    if (ck) save(ck);
    i64 w = 0; for (int k = 0; k < lp; k++) w += L[k]; for (int k = 0; k < rp; k++) w += R[k];
    printf("%s after %llu frames, ones %lld\n", status == 1 ? "CRITICAL FRAME (machine halts)" : status == 2 ? "FIXED FRAME (machine never halts)" : status == 3 ? "TOO MANY BLOCKS" : "no critical frame", (unsigned long long)n, (long long)w);
    dump(stdout);
#ifdef STATS
    printf("left-end zigzags on a block of m cells, m = 2..20:"); for (int k = 2; k <= 20; k++) printf(" %d:%llu", k, (unsigned long long)hist[k]); printf("\n");
    printf("the same by doubling of the number of ones (2^k):"); for (int k = 0; k < 80; k++) if (oct[k]) printf(" %d:%llu", k, (unsigned long long)oct[k]); printf("\n");
#endif
    return 0;
}
