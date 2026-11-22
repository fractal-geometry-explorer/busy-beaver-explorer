/* frun: the frame map `next` of lean/Phases.lean (78 cases, c/fcases.h generated from the Lean files by py/gen_c.py)
 * iterated from Ph.z 0 0 2 (init_start: 2 machine steps), with the sweeps and zigzag rounds taken in one jump each.
 *
 *   frun check N         N jumps, each compared with the same frames taken one case at a time (exit 1 on a mismatch)
 *   frun run N [EVERY]   N jumps; every EVERY jumps a line "jumps frames steps tag l j r"
 *   frun trace N         the first N jumps, one line each (for py/check_frun.py)
 *   frun stats N         N jumps, then the zigzag starts by class and by |delta + 1|, delta = a/3 - (r - 1)
 *   frun close N EVERY D N jumps (with the lines of run); print every zigzag start within D of a halting row (d = 0 halts):
 *                        y(3k+1, 2m, k+2+d) and Y(3k+1, 2m, k+3+d)
 *   frun rows B          from every frame with all values < B: do the halts within 400 jumps all come before the
 *                        first zigzag start or right after a zigzag start in a halting row (lean/Jump.lean)?
 *   frun near N          N jumps; at each zigzag start, which r -> r + e (|e| <= 6) halt within 12 jumps
 *
 * Jumps (each is k applications of one or two cases of next, with k the largest count for which every application
 * is still the first matching case; the step counts are the sums of the per-case counts of lean/Pieces.lean):
 *   w/W sweep   w(l, j, r), j >= 2, r >= 1     -> w(l + 4k, j - 2k, r), k = j / 2, 6k steps
 *   u sweep     u(l, j, r), j >= 1             -> u(l, 0, r + 2j), 4j steps    (U: l >= 1)
 *   zigzag      y(a, j, r), a >= 3, r >= 2     -> y(a - 3k, j + 2k, r - k), k = min(a / 3, r - 1),
 *                                                k(4j + 9) + 4k(k - 1) steps  (Y alike)
 * Every other frame is one case.  Values are 64-bit (exit 2 before an overflow); steps are 128-bit.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long long I;
typedef unsigned __int128 W;
#include "fcases.h"

static const char TAG[] = "zywuZYWU";
enum { z, y, w, u, Z, Y, Wt, U };

/* one jump; returns the number of frames (applications of next), 0 on a halt (then *hc is the halting case) */
static int zz_on = 1;
static I zz_n, zz_hist[2][3][2][64]; /* zigzag jumps; [Y?][a mod 3][j parity][bin of |delta + 1|] */
static I cur_jump, close_max = -1;
static void zz_note(int big, I a, I b, I c) {
    if (close_max >= 0 && a % 3 == 1 && !(b & 1)) {  /* the halting rows: y(3k+1, even, k+2), Y(3k+1, even, k+3) */
        I d = c - a / 3 - (big ? 3 : 2);
        if ((d < 0 ? -d : d) <= close_max) {
            printf("close jump %lld %c(%lld,%lld,%lld) d %+lld\n", cur_jump, big ? 'Y' : 'y', a, b, c, d); fflush(stdout);
        }
    }
    I d = a / 3 - (c - 1) + 1, m = d < 0 ? -d : d; int bin = 0;
    while (m) { bin++; m >>= 1; }
    zz_n++; zz_hist[big][a % 3][b & 1][bin]++;
}
static I jump(int *t, I v[3], W *st, int *hc) {
    I a = v[0], b = v[1], c = v[2], k;
    if ((*t == w || *t == Wt) && b >= 2 && c >= 1) {
        k = b / 2; v[0] = a + 4 * k; v[1] = b - 2 * k; *st = (W)6 * k; return k;
    }
    if ((*t == u && b >= 1) || (*t == U && a >= 1 && b >= 1)) {
        v[1] = 0; v[2] = c + 2 * b; *st = (W)4 * b; return b;
    }
    if ((*t == y || *t == Y) && a >= 3 && c >= 2) {
        if (zz_on) zz_note(*t == Y, a, b, c);
        k = a / 3; if (c - 1 < k) k = c - 1;
        v[0] = a - 3 * k; v[1] = b + 2 * k; v[2] = c - k;
        *st = (W)k * (W)(4 * b + 9) + (W)4 * k * (k - 1); return 2 * k;
    }
    int r = fc_step(t, v, st);
    if (r < 0) { *hc = -1 - r; return 0; }
    return 1;
}

static void pw(W x, char *buf) {   /* decimal */
    char tmp[64]; int n = 0;
    if (!x) { strcpy(buf, "0"); return; }
    while (x) { tmp[n++] = '0' + (int)(x % 10); x /= 10; }
    for (int i = 0; i < n; i++) buf[i] = tmp[n - 1 - i];
    buf[n] = 0;
}

/* does the map halt within J jumps from (t, v)? returns the halting case index or -1 */
static int halts_within(int t, I a, I b, I c, int J) {
    I v[3] = {a, b, c};
    for (int i = 0; i < J; i++) {
        W st; int hc = -1;
        if (v[0] < 0 || v[1] < 0 || v[2] < 0) return -1;
        if (jump(&t, v, &st, &hc) == 0) return hc;
    }
    return -1;
}

/* which halts do not pass a halting row? from every frame with all values < B, up to 400 jumps */
static int rows_main(I B) {
    {
        I tot = 0, viarow = 0, other = 0, shown = 0, direct = 0;
        for (int t0 = 0; t0 < 8; t0++) for (I a = 0; a < B; a++) for (I b = 0; b < B; b++) for (I c = 0; c < B; c++) {
            int t = t0; I v[3] = {a, b, c}; int row = 0, seen = 0;
            for (int i = 0; i < 400; i++) {
                if ((t == y || t == Y) && v[0] >= 3 && v[2] >= 2) { seen = 1;
                    I e3 = v[0] % 3, q = v[0] / 3;
                    row = (e3 == 1 && !(v[1] & 1) && v[2] == q + (t == Y ? 3 : 2)) || (e3 == 0 && (v[1] & 1) && v[2] == q + 2) || (t == y && e3 == 2 && (v[1] & 1) && v[2] == q + 2); }
                W st; int hc = -1;
                if (jump(&t, v, &st, &hc) == 0) {
                    tot++; if (!seen) direct++; else if (row) viarow++; else { other++; if (shown < 20) { shown++;
                        printf("other: %c(%lld,%lld,%lld) halts by %s at jump %d\n", TAG[t0], a, b, c, fc_name[hc], i + 1); } }
                    break;
                }
            }
        }
        printf("start frames < %lld: %lld halt within 400 jumps: %lld before any zigzag, %lld with the last zigzag start a halting row, %lld otherwise\n", B, tot, direct, viarow, other);
        return 0;
    }
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: frun check|run|trace N [EVERY]\n"); return 1; }
    const char *mode = argv[1];
    if (!strcmp(mode, "rows")) return rows_main(atoll(argv[2]));
    I N = atoll(argv[2]), every = argc > 3 ? atoll(argv[3]) : 0;
    int t = z; I v[3] = {0, 0, 2};
    W frames = 0, steps = 2;
    I vmax = 0;
    char b1[64], b2[64];
    zz_on = !strcmp(mode, "stats") || !strcmp(mode, "close");
    if (!strcmp(mode, "close")) close_max = argc > 4 ? atoll(argv[4]) : 8;
    for (I i = 1; i <= N; i++) {
        int t0 = t; I v0[3] = {v[0], v[1], v[2]};
        cur_jump = i;
        if (!strcmp(mode, "near") && (t == y || t == Y) && v[0] >= 3 && v[2] >= 2) {
            /* zigzag start: which changes r -> r + e (|e| <= 6) of the solid block halt within 12 jumps? */
            char hb[64]; int nh = 0, best = 99; hb[0] = 0;
            for (int e = -6; e <= 6; e++) {
                if (v[2] + e < 2) continue;
                int h = halts_within(t, v[0], v[1], v[2] + e, 12);
                if (h >= 0) { nh++; if ((e < 0 ? -e : e) < best) best = e < 0 ? -e : e; sprintf(hb + strlen(hb), " %+d", e); }
            }
            if (nh && best <= 1) printf("near jump %lld %c(%lld,%lld,%lld) halting e:%s\n", i, TAG[t], v[0], v[1], v[2], hb);
        }
        W st = 0; int hc = -1;
        I k = jump(&t, v, &st, &hc);
        if (k == 0) {
            frames += 1; steps += st;
            pw(frames, b1); pw(steps, b2);
            printf("HALT jump %lld frame %s steps %s case %s from %c(%lld,%lld,%lld)\n", i, b1, b2, fc_name[hc],
                   TAG[t0], v0[0], v0[1], v0[2]);
            return 0;
        }
        if (!strcmp(mode, "check") && k > 1) {    /* the same k frames one case at a time */
            int tt = t0; I vv[3] = {v0[0], v0[1], v0[2]}; W s2 = 0;
            for (I m = 0; m < k; m++) {
                W s1; int r = fc_step(&tt, vv, &s1);
                if (r < 0) { printf("MISMATCH halt inside jump %lld\n", i); return 1; }
                s2 += s1;
            }
            if (tt != t || vv[0] != v[0] || vv[1] != v[1] || vv[2] != v[2] || s2 != st) {
                printf("MISMATCH jump %lld from %c(%lld,%lld,%lld)\n", i, TAG[t0], v0[0], v0[1], v0[2]); return 1;
            }
        }
        frames += k; steps += st;
        for (int q = 0; q < 3; q++) if (v[q] > vmax) vmax = v[q];
        if (vmax > (1LL << 60)) { printf("OVERFLOW at jump %lld\n", i); return 2; }
        if (!strcmp(mode, "trace")) {
            pw(frames, b1); pw(steps, b2);
            printf("%s %s %c %lld %lld %lld\n", b1, b2, TAG[t], v[0], v[1], v[2]);
        } else if (every && i % every == 0 && strcmp(mode, "check")) {
            pw(frames, b1); pw(steps, b2);
            printf("%lld %s %s %c %lld %lld %lld\n", i, b1, b2, TAG[t], v[0], v[1], v[2]); fflush(stdout);
        }
    }
    if (!strcmp(mode, "stats")) {   /* zigzag starts by |delta + 1| (delta = a/3 - (r - 1); 0 is the halting row) */
        printf("zigzag jumps %lld; rows: tag a%%3 j%%2, then counts with |delta+1| = 0, 1, 2-3, 4-7, ...\n", zz_n);
        for (int g = 0; g < 2; g++) for (int e = 0; e < 3; e++) for (int p = 0; p < 2; p++) {
            printf("%c %d %d:", g ? 'Y' : 'y', e, p);
            for (int q = 0; q < 40; q++) printf(" %lld", zz_hist[g][e][p][q]);
            printf("\n");
        }
    }
    pw(frames, b1); pw(steps, b2);
    printf("END jumps %lld frames %s steps %s state %c(%lld,%lld,%lld) max %lld\n", N, b1, b2, TAG[t], v[0], v[1], v[2], vmax);
    return 0;
}
