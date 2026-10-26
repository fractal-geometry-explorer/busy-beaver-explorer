#include "model_core_r.h"
#include <string.h>
/* Every loop-shaped round start G 1, W a, W b, W c with width E in [Emin, Emax] (valid parities, separations >= 4):
   does the real machine halt, and does the mark model's right-end run reach a meeting distance d <= 2? */
static const int WR[6][2] = {{1,0},{1,0},{1,1},{1,0},{0,0},{0,1}};
static const int MVv[6][2] = {{1,1},{-1,1},{-1,-1},{-1,0},{1,-1},{-1,1}};
static const int NXt[6][2] = {{1,4},{2,0},{0,3},{0,-1},{5,1},{3,4}};
static unsigned char tp[1 << 16];
static int tm_halts(int a, int b, int c, int E) {
    memset(tp, 0, sizeof tp); int base = 4000; int prev = 1; tp[base] = 1; tp[base + 1] = tp[base + 2] = tp[base + 3] = 0; prev = 0;
    int mk[3] = {a, b, c}, mi = 0;
    for (int i = 4; i < E; i++) { int v; if (mi < 3 && i == mk[mi] + 1) { v = prev; mi++; } else v = 1 - prev; if (mi < 3 && i == mk[mi] && v != 0) return -1; tp[base + i] = v; prev = v; }
    if (prev != 1) return -1;
    long h = base + 3, lo = base, hi = base + E - 1; int st = 4; long steps = 0, cap = 4000L * E * E;
    while (steps < cap) {
        int sym = tp[h];
        if (steps > 0 && st == 0 && sym == 1 && tp[h + 1] == 1 && !tp[h - 1] && !tp[h - 2]) {
            int lb = 1; for (long i = lo; i < h; i++) if (tp[i]) { lb = 0; break; }
            if (lb) { long i = h + 2; while (tp[i] == 1 && tp[i + 1] == 0) i += 2;
                if (tp[i] == 1 && tp[i + 1] == 1) { int rb = 1; for (long j = i + 2; j <= hi + 1; j++) if (tp[j]) { rb = 0; break; } if (rb) return 0; } }
        }
        int nx = NXt[st][sym]; if (nx < 0) return 1;
        tp[h] = WR[st][sym]; h += MVv[st][sym]; st = nx; steps++; if (h < lo) lo = h; if (h > hi) hi = h;
        if (h < 10 || h > (1 << 16) - 10) return 2;
    }
    return 2;
}
static int model_close(int a, int b, int c, int E) {
    nm = 0; halted = 0; bad = 0; nend = 0; W = E; add('W', a); add('W', b); add('W', c); add('G', 1);
    for (int r = 1; r <= 400; r++) { CUR_RD = r; do_round(); if (halted) return 2; if (bad) return 3;
        for (int i = 0; i < nend; i++) if (endd[i] <= 2) return 1;
        int alive = 0, ok = 0; for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M' && P[i] == W - 2) ok = 1; }
        if (alive == 2 && ok) return 0; }
    return 0;
}
int main(int argc, char **argv) {
    int Emin = atoi(argv[1]), Emax = atoi(argv[2]);
    long tab[4][4] = {{0}}; long tot = 0; int shown = 0;
    for (int E = Emin; E <= Emax; E += 2)
        for (int a = 7; a < E; a += 2) for (int b = a + 5; b < E; b += 2) for (int c = b + 5; c < E - 3; c += 2) {
            int t = tm_halts(a, b, c, E); if (t < 0) continue;
            int mpred = model_close(a, b, c, E);
            tab[t][mpred]++; tot++;
            if (((t == 1) != (mpred == 1)) && shown < 10) { shown++; printf("  disagree: a %d b %d c %d E %d: machine %s, model %s\n", a, b, c, E, t == 1 ? "halts" : t == 0 ? "clean" : "cap", mpred == 1 ? "reaches d<=2" : mpred == 0 ? "clean" : mpred == 2 ? "halt" : "bad"); }
        }
    printf("%ld states with E in [%d, %d]\n", tot, Emin, Emax);
    printf("machine \\ model:   clean   reaches d<=2   model-halt   model-bad\n");
    const char *rn[3] = {"clean", "halts", "cap"};
    for (int t = 0; t < 3; t++) printf("  %-8s %9ld %14ld %12ld %11ld\n", rn[t], tab[t][0], tab[t][1], tab[t][2], tab[t][3]);
}
