/* rules_check: c/trans.c, plus a check of the Lean rules of lean/Subround.lean at every sub-round it simulates.
 *
 * At every moment the head is in C on a 0 just right of a 1, it looks at the cells near the head and decides which
 * rule of lean/Subround.lean applies (glong, gshort, gzero, single, singleone); the next such moment must then come exactly the
 * rule's number of steps later (else a line "BAD" on stderr).  Where no rule applies it writes a line "EXC kind ..."
 * on stderr (kind: small = the carry meets a small gap, interior = the last interior block is not 2 mod 3, single-l
 * = a single block with last block below 5), with the nearest blocks (nearest first) and the zone's gaps.  At the
 * end: "SUM moments=... exc=... bad=...".  Input, output and the stop rule are those of c/trans.c:
 *
 * trans MACHINE MAXSTEPS R P Q U L0 AUX < config
 *                         (two lines on stdin: "b1 b2 ... bk l" and "g1 g2 ..."; the second may be empty)
 *
 * Writes the tape  1^b1 0 1^b2 0 ... 0 1^l C>0 zone,  where the zone is 0^g1 1 0^g2 1 ... (g1 counts the head's cell),
 * and runs the machine from there, cell by cell, to the first later moment of the same shape (head in C on a 0 just
 * right of a 1, no two 0s in a row left of the head) at which
 *   - the blocks are regular: at least two interior blocks, the first a multiple of P, the others Q mod P; then, if
 *     AUX > 0, one block of exactly AUX cells; then the last block l with l >= L0 and l = L0 mod U; and
 *   - the zone is regular (g1 a positive multiple of U, the other gaps U - 1 mod U), or its leading regular gaps
 *     allow at least R more regular sub-rounds (py/model.py explains the count).
 * For this machine P Q U L0 AUX = 3 2 4 1 0.
 * Prints "reg STEPS" or "part STEPS" and the configuration "b1 ... bk | l | g1 g2 ...", or "HALT STEPS" (bbchallenge
 * count), or "max STEPS".  Nothing is assumed about the machine: every step is a step of the transition table. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int W[6][2], D[6][2], N[6][2];
static long long *readline_ll(long long *n) {
    size_t cap = 1 << 16, len = 0; char *s = malloc(cap); int c;
    while ((c = getchar()) != EOF && c != '\n') { if (len + 2 > cap) s = realloc(s, cap *= 2); s[len++] = (char)c; }
    s[len] = 0;
    long long *v = malloc(sizeof(long long) * (len / 2 + 2)); *n = 0;
    char *q = s;
    for (;;) { while (*q == ' ' || *q == ',') q++; if (!*q) break; v[(*n)++] = strtoll(q, &q, 10); }
    free(s); return v;
}
static long long expect = -1, lastk = -1, nbad = 0, nexc = 0, nmom = 0;
static char pending[512];   /* the EXC line of the sub-round in progress, written once it is complete */
/* the rule of lean/Subround.lean that applies at a sub-round moment, its step count checked at the next moment */
static void classify(unsigned char *t, long long head, long long lo, long long hi, long long k) {
            {
                long long i = head - 1; while (t[i]) i--;
                long long l = head - 1 - i, sep = i, pend = sep - 1, ps = pend; while (ps >= 0 && t[ps]) ps--;
                long long p = pend - ps;           /* block before the separator, p = 0 if none */
                long long pred = -1; const char *kind = 0;
                int leftblank = 1; for (long long j = lo; j <= ps; j++) if (t[j]) { leftblank = 0; break; }
                if (p > 0 && p % 3 == 2 && 1) {
                    long long a = (p - 2) / 3;
                    if (l >= 2) { pred = 12 * a + (l - 2) + 21; }
                    else {
                        long long q = head + 1, n = 0; int res = 0;   /* res 1 ok, 2 small */
                        for (;;) {
                            long long u = 0; while (q <= hi + 4 && t[q] == 0 && u < 4) { u++; q++; }
                            if (u >= 4) { res = 1; break; }
                            if (q > hi + 4) { res = 1; break; }
                            if (u == 3) { n++; q++; continue; }
                            if (u == 0) {              /* gzero: the next gap has at least 2 cells, or blank */
                                long long q2 = q + 1, w = 0; while (q2 <= hi + 4 && t[q2] == 0 && w < 2) { w++; q2++; }
                                if (w >= 2) { res = 3; break; }
                            }
                            res = 2; kind = "small"; break;
                        }
                        if (res == 1) pred = 12 * a + 6 * n + 26;
                        if (res == 3) pred = 12 * a + 6 * n + 27;
                    }
                } else if (p > 0 && p % 3 == 0 && leftblank && l >= 5) {
                    pred = (l - 5) + 12 * (p / 3 - 1) + 33;
                } else if (p > 0 && p % 3 == 0 && leftblank && l == 1 && t[head + 1] == 0 && t[head + 2] == 0) {
                    pred = 12 * (p / 3 - 1) + 30;                  /* singleone */
                } else kind = (p > 0 && p % 3 == 0 && leftblank) ? "single-l" : "interior";
                /* the sub-round that started at the previous moment is complete: count and check it */
                if (lastk >= 0) {
                    nmom++;
                    if (expect >= 0 && k - lastk != expect) { nbad++; fprintf(stderr, "BAD rule predicted %lld steps, took %lld\n", expect, k - lastk); }
                    if (expect < 0) { nexc++; fputs(pending, stderr); }
                }
                pending[0] = 0;
                if (pred < 0) {
                    if (!kind) kind = "small";
                    char *o = pending; size_t room = sizeof pending;
                    int w = snprintf(o, room, "EXC %s l=%lld blocks:", kind, l); o += w; room -= w;
                    long long c = 0, run2 = 0;
                    for (long long z = sep - 1; z >= lo && c < 6; z--) { if (t[z]) run2++; else { if (run2 == 0) break; w = snprintf(o, room, " %lld", run2); o += w; room -= w; run2 = 0; c++; } }
                    if (run2) { w = snprintf(o, room, " %lld%s", run2, c < 6 ? "(first)" : ""); o += w; room -= w; }
                    w = snprintf(o, room, " gaps:"); o += w; room -= w;
                    long long g = 0; c = 0; for (long long z = head; z <= hi && c < 8; z++) { if (t[z] == 0) g++; else { w = snprintf(o, room, " %lld", g); o += w; room -= w; g = 0; c++; } }
                    snprintf(o, room, "\n");
                }
                expect = pred; lastk = k;
            }
}
int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: trans MACHINE MAXSTEPS R P Q U L0 AUX < config\n"); return 1; }
    long long P = atoll(argv[4]), Q = atoll(argv[5]), U = atoll(argv[6]), L0 = atoll(argv[7]), AUX = atoll(argv[8]);
    char *m = argv[1];
    for (int s = 0; s < 6; s++) for (int b = 0; b < 2; b++) {
        char *t = m + 7 * s + 3 * b;
        if (t[0] == '-') { N[s][b] = -1; continue; }
        W[s][b] = t[0] - '0'; D[s][b] = t[1] == 'R' ? 1 : -1; N[s][b] = t[2] - 'A';
    }
    long long max = atoll(argv[2]); double R = atof(argv[3]);
    long long nb0, ng0; long long *bl = readline_ll(&nb0), *gp = readline_ll(&ng0);
    long long tot = 0; for (long long i = 0; i < nb0; i++) tot += bl[i] + 1; for (long long i = 0; i < ng0; i++) tot += gp[i] + 1;
    long long O = 1 << 22, size = O + tot + (1 << 22); unsigned char *t = calloc(size, 1);
    long long pos = O;
    for (long long i = 0; i < nb0; i++) { for (long long j = 0; j < bl[i]; j++) t[pos++] = 1; if (i < nb0 - 1) pos++; }
    long long head = pos, pp = head;
    for (long long i = 0; i < ng0; i++) { pp += gp[i]; t[pp++] = 1; }
    long long lo = O, hi = pp, k = 0; int st = 2;
    classify(t, head, lo, hi, 0);
    while (k < max) {
        int b = t[head];
        if (N[st][b] < 0) { printf("HALT %lld\n", k + 1); return 0; }
        t[head] = W[st][b]; head += D[st][b]; st = N[st][b]; k++;
        if (head < lo) lo = head;
        if (head > hi) hi = head;
        if (head < 8 || head > size - 8) { printf("OUT %lld\n", k); return 0; }

        if (st == 2 && t[head] == 0 && t[head - 1] == 1) {
            classify(t, head, lo, hi, k);
            long long a = lo, i, run = 0, nb = 0; int ok = 1;
            /* a cheap test first, on the cells next to the head: the last block and the AUX block */
            i = head - 1; while (i >= lo && t[i]) i--;
            run = head - 1 - i;
            if (run < L0 || (run - L0) % U != 0) continue;
            if (AUX > 0) { long long j = i - 1; while (j >= lo && t[j]) j--; if (i - 1 - j != AUX) continue; }
            run = 0;
            while (t[a] == 0) a++;
            long long prev = -1;                 /* the block before the current one, checked one block late */
            for (i = a; i < head && ok; i++) {
                if (t[i]) run++;
                else {
                    if (run == 0) { ok = 0; break; }
                    if (prev >= 0 && (nb == 1 ? prev % P != 0 : prev % P != Q)) ok = 0;
                    prev = run; nb++; run = 0;
                }
            }
            /* prev is the last block before l: the AUX block if AUX > 0, else an interior block */
            if (!ok || prev < 0) continue;
            if (AUX > 0) { if (prev != AUX) continue; nb--; }
            else if (nb == 1 ? prev % P != 0 : prev % P != Q) continue;
            if (run < L0 || (run - L0) % U != 0 || nb < 2) continue;
            long long l = run, e = hi, g = 0, tz = (l - L0) / U; int first = 1, reg = 1; double rem = 0, w = 1;
            while (e > head && t[e] == 0) e--;
            for (i = 0; i < tz && i < 1100; i++) w *= 2;                /* 2^tz; saturates at infinity, which is fine */
            for (i = head; i <= e; i++) {
                if (t[i] == 0) { g++; continue; }
                if (reg) {
                    long long seg = first ? g : g + 1;
                    if (seg % U != 0 || seg < U) reg = 0;
                    else {
                        long long n = seg / U, j = 0;
                        if (!first) { w *= 2; j = 1; }
                        for (; j < n && j < 1100; j++) { rem += w; w *= 2; }
                    }
                }
                first = 0; g = 0;
            }
            if (!(reg || rem - 1 >= R)) continue;
            fprintf(stderr, "SUM moments=%lld exc=%lld bad=%lld\n", nmom, nexc, nbad); printf("%s %lld\n", reg ? "reg" : "part", k); run = 0;
            for (i = a; i < head; i++) { if (t[i]) run++; else { printf("%lld ", run); run = 0; } }
            printf("| %lld |", run);
            g = 0; for (i = head; i <= e; i++) { if (t[i] == 0) g++; else { printf(" %lld", g); g = 0; } }
            printf("\n"); return 0;
        }
    }
    printf("max %lld\n", k); return 0;
}
