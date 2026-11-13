/* tmfrom MACHINE "TAPE" MAXSTEPS STATE SIDE K : run from an RLE tape ("1^2 0 C>0 1^5"), print the tape each time
   the head is in STATE at the SIDE (L/R) end of the visited/initial region, at most K times; then "halted N" or
   "running N". Tape outside the given cells is blank. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define SZ (1<<22)
static unsigned char tape[SZ];
int W[6][2], MV[6][2], NS[6][2];
long lo, hi;
void show(long h, int st, long long n) {
    printf("%lld ", n);
    long a = lo, b = hi;
    while (a < h && tape[a] == 0) a++;
    while (b > h && tape[b] == 0) b--;
    long i = a;
    while (i <= b) {
        if (i == h) { printf("%c>", 'A' + st); }
        long j = i; while (j <= b && tape[j] == tape[i] && (j == i || j != h)) j++;
        if (i < h && j > h) j = h;
        if (j - i == 1) printf("%d ", tape[i]); else printf("%d^%ld ", tape[i], j - i);
        i = j;
    }
    printf("\n");
}
int main(int argc, char **argv) {
    char *m = argv[1];
    for (int s = 0; s < 6; s++) for (int b = 0; b < 2; b++) {
        char *t = m + s * 7 + b * 3;
        if (t[2] == '-' || t[2] == 'Z') { NS[s][b] = -1; continue; }
        W[s][b] = t[0] - '0'; MV[s][b] = t[1] == 'R' ? 1 : -1; NS[s][b] = t[2] - 'A';
    }
    long pos = SZ / 2, h = -1; int st = 0;
    char *s = strdup(argv[2]); char *tok = strtok(s, " ");
    long start = pos;
    while (tok) {
        char *p = tok;
        if (strchr(p, '>')) { st = p[0] - 'A'; h = pos; p = strchr(p, '>') + 1; }
        int v = p[0] - '0'; long c = 1;
        if (p[1] == '^') c = atol(p + 2);
        for (long i = 0; i < c; i++) tape[pos++] = v;
        tok = strtok(NULL, " ");
    }
    lo = start; hi = pos - 1;
    long long max = atoll(argv[3]); int est = argv[4][0] - 'A'; int side = argv[5][0] == 'R'; long K = atol(argv[6]);
    long long n = 0; long cnt = 0; int halted = 0;
    while (n < max) {
        int b = tape[h];
        if (NS[st][b] < 0) { n++; halted = 1; break; }
        tape[h] = W[st][b]; h += MV[st][b]; st = NS[st][b]; n++;
        if (h < lo) lo = h; if (h > hi) hi = h;
        if (h < 1 || h >= SZ - 1) { printf("out of tape\n"); return 1; }
        if (K > 0 && st == est && h == (side ? hi : lo)) { show(h, st, n); if (K > 0 && ++cnt >= K) break; }
    }
    if (halted) { printf("halted %lld ", n); show(h, st, n); } else printf("running %lld\n", n);
    return 0;
}
