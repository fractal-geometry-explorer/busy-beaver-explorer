#include <stdio.h>
#include <string.h>
typedef long long ll;
typedef struct {
    long long settled, open2, hist[64], jh[64], direct, dbad, bad;
    ll jminmax, jminmax_rho, Jmax, Jmax_n; int dmax; ll dmax_n; int newmax;
    ll ms[3][4][4], msn[3][4][4];
} Stats;
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "rb"); Stats G; fread(&G, sizeof G, 1, f); fclose(f);
    printf("settled %lld direct %lld dbad %lld bad %lld Jmax %lld (n=%lld) newmax %d jminmax %lld\n", G.settled, G.direct, G.dbad, G.bad, G.Jmax, G.Jmax_n, G.newmax, G.jminmax);
    const char *ph[3] = {"gap", "shift", "packet"}, *nmT = "GMWB";
    for (int a = 0; a < 3; a++) for (int x = 0; x < 4; x++) for (int y = 0; y < 4; y++)
        if (G.ms[a][x][y] < (1LL << 62)) printf("  %s %c%c min %lld (n=%lld)\n", ph[a], nmT[x], nmT[y], G.ms[a][x][y], G.msn[a][x][y]);
}
