/* chk MACHINE STEPS: the plain machine from blank tape for exactly STEPS steps; prints "CHECK steps state head ones hash" as msim does. */
#include <stdio.h>
#include <stdlib.h>
int main(int argc, char **argv) {
    const char *m = argv[1]; unsigned long long mx = strtoull(argv[2], 0, 10); int W[6][2], D[6][2], S[6][2];
    for (int s = 0; s < 6; s++) for (int b = 0; b < 2; b++) { const char *p = m + 7 * s + 3 * b; if (p[0] == '-') { S[s][b] = -1; continue; } W[s][b] = p[0] - '0'; D[s][b] = p[1] == 'R' ? 1 : -1; S[s][b] = p[2] - 'A'; }
    long N = 1L << 28; unsigned char *t = calloc(N, 1); long pos = N / 2; int st = 0;
    for (unsigned long long i = 0; i < mx; i++) { int b = t[pos]; if (S[st][b] < 0) { printf("HALT %llu\n", i + 1); return 0; } t[pos] = W[st][b]; int d = D[st][b]; st = S[st][b]; pos += d; }
    long a = 0, z = N - 1; while (a < N && !t[a]) a++; while (z >= 0 && !t[z]) z--;
    unsigned long long h = 0, ones = 0; for (long i = a; i <= z; i++) { h = h * 1000003ULL + t[i]; ones += t[i]; }
    printf("CHECK %llu %c %ld %llu %llu\n", mx, 'A' + st, pos - a, ones, h); return 0;
}
