/* trans MACHINE MAXSTEPS R P Q U L0 AUX < config
 *                         (two lines on stdin: "b1 b2 ... bk l" and "g1 g2 ..."; the second may be empty)
 *
 * Writes the tape  1^b1 0 1^b2 0 ... 0 1^l C>0 zone,  where the zone is 0^g1 1 0^g2 1 ... (g1 counts the head's cell),
 * and runs the machine from there, cell by cell, to the first later moment of the same shape (head in C on a 0 just
 * right of a 1, no two 0s in a row left of the head) at which
 *   - the blocks are regular: at least two interior blocks, the first a multiple of P, the others Q mod P; then, if
 *     AUX > 0, one block of exactly AUX cells; then the last block l with l >= L0 and l = L0 mod U; and
 *   - the zone is regular (g1 a positive multiple of U, the other gaps U - 1 mod U), or its leading regular gaps
 *     allow at least R more regular sub-rounds (py/model.py explains the count).
 * For this machine P Q U L0 AUX = 2 1 5 5 1.
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
    while (k < max) {
        int b = t[head];
        if (N[st][b] < 0) { printf("HALT %lld\n", k + 1); return 0; }
        t[head] = W[st][b]; head += D[st][b]; st = N[st][b]; k++;
        if (head < lo) lo = head;
        if (head > hi) hi = head;
        if (head < 8 || head > size - 8) { printf("OUT %lld\n", k); return 0; }
        if (st == 2 && t[head] == 0 && t[head - 1] == 1) {
            long long a = lo, i, run = 0, nb = 0; int ok = 1;
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
            printf("%s %lld\n", reg ? "reg" : "part", k); run = 0;
            for (i = a; i < head; i++) { if (t[i]) run++; else { printf("%lld ", run); run = 0; } }
            printf("| %lld |", run);
            g = 0; for (i = head; i <= e; i++) { if (t[i] == 0) g++; else { printf(" %lld", g); g = 0; } }
            printf("\n"); return 0;
        }
    }
    printf("max %lld\n", k); return 0;
}
