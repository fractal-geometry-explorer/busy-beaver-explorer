// transcount: how often does a run from blank tape use one entry of the table, and when?
//
//   transcount MACHINE MAX_STEPS ENTRY [K]     ENTRY like E0 (state E reading 0)
//
// Prints the step numbers (0-based: the number of steps made before) of the first K uses (default 20) and the
// number of uses at every power of ten of steps.  Used in round 6 to see whether the entry in which this machine
// differs from the machines proved in busycoq is ever reached: it is, from the first steps on.
#include <cstdio>
#include <cstdlib>
#include <vector>
int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: transcount MACHINE MAX_STEPS ENTRY [K]\n"); return 1; }
    const char *m = argv[1]; long maxs = atol(argv[2]); int qs = argv[3][0] - 'A', bs = argv[3][1] - '0';
    int K = argc > 4 ? atoi(argv[4]) : 20;
    int W[6][2], D[6][2], N[6][2], H[6][2] = {};
    for (int i = 0; i < 6; i++) for (int b = 0; b < 2; b++) {
        const char *t = m + i * 7 + b * 3;
        if (t[0] == '-') H[i][b] = 1; else { W[i][b] = t[0] - '0'; D[i][b] = t[1] == 'R'; N[i][b] = t[2] - 'A'; }
    }
    long sz = 1 << 24; std::vector<char> t(sz, 0); long pos = sz / 2; int q = 0; long cnt = 0, nx = 10;
    for (long s = 0; s < maxs; s++) {
        int x = t[pos];
        if (H[q][x]) { printf("HALT %ld\n", s); return 0; }
        if (q == qs && x == bs) { cnt++; if (cnt <= K) printf("use %ld at step %ld\n", cnt, s); }
        t[pos] = W[q][x]; int d = D[q][x]; q = N[q][x]; pos += d ? 1 : -1;
        if (pos < 8 || pos > sz - 8) { printf("tape overflow\n"); return 1; }
        if (s + 1 == nx) { printf("steps %ld uses %ld\n", nx, cnt); nx *= 10; }
    }
    return 0;
}
