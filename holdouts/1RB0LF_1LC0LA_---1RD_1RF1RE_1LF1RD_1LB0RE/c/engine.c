/* engine.c: the regular left part and the irregular right part ("engine") of
 * 1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE, sampled at every visit to a new leftmost cell (one per pass).
 *
 * At such a visit the tape is  [A]0 (011)^4 (1011011011)^k I  with I the engine (everything right of the blocks).
 * Reported over the whole run:
 *   - k: how often it grew and how often it shrank between consecutive passes;
 *   - |I|: its range; whether any I (with its offset mod 10 against the blocks) ever repeated (hash);
 *   - emitter: the longest common prefix of I with I seven passes earlier (minimum over passes > 300);
 *   - crossings: at the cell boundary OFF cells inside the block region (measured at the previous pass), the
 *     distinct sequences of crossings in one pass ('>' right, '<' left, then the state entered).
 *
 * usage: gcc -O2 -o engine engine.c && ./engine STEPS [OFF]      (1e10 steps: about a minute, 47,331 passes)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static const int W[6][2] = {{1, 0}, {1, 0}, {-1, 1}, {1, 1}, {1, 1}, {1, 0}};
static const int Mv[6][2] = {{1, -1}, {-1, -1}, {0, 1}, {1, 1}, {-1, 1}, {-1, 1}};
static const int Nx[6][2] = {{1, 5}, {2, 0}, {-1, 3}, {5, 4}, {5, 3}, {1, 4}};
#define SZ (1L << 25)
static unsigned char tape[SZ];
static const char *B = "1011011011";
#define HS (1 << 22)
static unsigned long long hk[HS];
#define HIST 8
static char hist[HIST][8192];
static char seqs[256][256]; static long cnts[256]; static int ns = 0;
int main(int argc, char **argv) {
    long steps = (long)atof(argv[1]); long off = argc > 2 ? atol(argv[2]) : 20;
    long pos = SZ / 2, lo = pos, hi = pos, pass = 0, pk = 0, inc = 0, dec = 0, minI = 1 << 30, maxI = 0, reps = 0;
    long minpre = 1 << 30, x = -1; int s = 0, cl = 0; char cur[256];
    for (long t = 0; t < steps; t++) {
        int r = tape[pos];
        if (Nx[s][r] < 0) { printf("HALT at step %ld\n", t); return 0; }
        long old = pos; int m = Mv[s][r];
        tape[pos] = W[s][r]; pos += m; s = Nx[s][r];
        if (pos > hi) hi = pos;
        if (x >= 0 && cl < 250) {
            if (old == x && pos == x - 1) { cur[cl++] = '<'; cur[cl++] = "ABCDEF"[s]; }
            if (old == x - 1 && pos == x) { cur[cl++] = '>'; cur[cl++] = "ABCDEF"[s]; }
        }
        if (pos >= lo) continue;
        lo = pos; pass++;
        long i = lo + 13, k = 0;
        while (i + 10 < hi) {
            int ok = 1;
            for (int q = 0; q < 10; q++) if (tape[i + q] != B[q] - '0') { ok = 0; break; }
            if (!ok) break;
            i += 10; k++;
        }
        if (pass > 1) { if (k > pk) inc++; if (k < pk) { dec++; printf("k shrank at pass %ld (step %ld): %ld -> %ld\n", pass, t, pk, k); } }
        pk = k;
        long len = hi - i + 1;
        if (pass > 100) { if (len < minI) minI = len; if (len > maxI) maxI = len; }
        if (pass > 10) {
            unsigned long long h = 1469598103934665603ULL;
            for (long j = i; j <= hi; j++) { h ^= tape[j] + 2; h *= 1099511628211ULL; }
            h ^= (unsigned long long)((i - lo) % 10) * 7919 + 1;
            unsigned long long b = h & (HS - 1);
            while (hk[b] && hk[b] != h) b = (b + 1) & (HS - 1);
            if (hk[b] == h) reps++; else hk[b] = h;
        }
        char *hh = hist[pass % HIST]; long L = 0;
        for (long j = i; j <= hi && L < 8000; j++) hh[L++] = '0' + tape[j];
        hh[L] = 0;
        if (pass > 300) {
            char *g = hist[(pass - 7) % HIST]; long c = 0;
            while (g[c] && hh[c] && g[c] == hh[c]) c++;
            if (c < minpre) minpre = c;
        }
        if (x >= 0 && pass > 300) {
            cur[cl] = 0; int j;
            for (j = 0; j < ns; j++) if (!strcmp(seqs[j], cur)) break;
            if (j == ns && ns < 256) strcpy(seqs[ns++], cur);
            if (j < 256) cnts[j]++;
        }
        x = k > 5 ? i - off : -1; cl = 0;
    }
    printf("steps %.3g, passes %ld, k = %ld (grew %ld times, shrank %ld times)\n", (double)steps, pass, pk, inc, dec);
    printf("engine length after pass 100: %ld..%ld; engines (with their offset mod 10) seen twice after pass 10: %ld\n", minI, maxI, reps);
    printf("emitter: after pass 300, I agrees with I seven passes earlier on at least its first %ld cells\n", minpre);
    printf("crossing sequences per pass at %ld cells inside the blocks (after pass 300):\n", off);
    for (int j = 0; j < ns; j++) printf("  %8ld  %s\n", cnts[j], seqs[j]);
    return 0;
}
