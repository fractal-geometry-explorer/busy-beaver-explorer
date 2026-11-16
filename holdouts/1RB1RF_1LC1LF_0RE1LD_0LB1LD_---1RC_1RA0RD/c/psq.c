/* psq.c: `next` of lean/Phases.lean of 1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD, from PS 0 2.
   usage: psq PHASES REPORT CKPT [trace N] */
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
typedef long long ll; typedef unsigned long long ull;
int main(int argc, char **argv) {
    ull N = strtoull(argv[1], 0, 10), Rp = strtoull(argv[2], 0, 10); const char *ck = argv[3]; ull trace = argc > 5 ? strtoull(argv[5], 0, 10) : 0;
    int ps = 1; ll a = 0, m = 0, c = 2; ull i = 0, npass = 0, neven = 0; ll minc = -1; ull minc_at = 0;
    FILE *in = fopen(ck, "r");
    if (in) { if (fscanf(in, "%llu %d %lld %lld %lld %llu %llu %lld %llu", &i, &ps, &a, &m, &c, &npass, &neven, &minc, &minc_at) != 9) return 4; fclose(in); }
    time_t t0 = time(0);
    for (; i < N; i++) {
        if (trace && i < trace) { if (ps) printf("%llu ps %lld %lld\n", i, a, c); else printf("%llu q %lld %lld %lld\n", i, a, m, c); }
        if (ps) {
            npass++;
            if (c % 2 == 0) neven++;
            if (i > 1000 && (minc < 0 || c < minc)) { minc = c; minc_at = i; }
            if (c <= 1) { printf("HALT: phase %llu is PS %lld %lld\n", i, a, c); FILE *o = fopen("HALT_FOUND", "a"); fprintf(o, "psq phase %llu PS %lld %lld\n", i, a, c); fclose(o); return 1; }
            if (a == 0 && c == 2) { c = 5; continue; }
            if (a == 0) { a = 2; c = c - 2; continue; }
            ps = 0; m = 2; a = a - 1; continue;          /* Q a 2 c, a = R */
        }
        ll R = a;
        if (R >= 1 && m >= 2 && c >= 3) { ll j = R < (c - 1) / 2 ? R : (c - 1) / 2; a = R - j; m = m + 2 * j; c = c - 2 * j; continue; }
        if (R == 0 && m >= 2 && c >= 5) { ps = 1; a = m + 2; c = c - 4; continue; }
        if (R == 0 && m >= 2 && c >= 1 && c <= 4) { ll mm = m - 2; ll t[5] = {0, 2 * mm + 8, 2 * mm + 6, 2 * mm + 11, 2 * mm + 9}; ps = 1; a = 0; c = t[c]; continue; }
        if (R == 1 && m >= 2 && (c == 1 || c == 2)) { ll mm = m - 2; ps = 1; a = 2; c = c == 1 ? 2 * mm + 6 : 2 * mm + 4; continue; }
        if (R >= 2 && m >= 2 && (c == 1 || c == 2)) { ll mm = m - 2; a = R - 2; m = 2; c = c == 1 ? 2 * mm + 8 : 2 * mm + 6; continue; }
        printf("NONE at q %lld %lld %lld (phase %llu)\n", R, m, c, i); return 2;
    }
    if (!trace || 1) {
        FILE *o = fopen("psq.tmp", "w"); fprintf(o, "%llu %d %lld %lld %lld %llu %llu %lld %llu\n", i, ps, a, m, c, npass, neven, minc, minc_at); fclose(o); rename("psq.tmp", ck);
    }
    printf("done %llu phases, no halt: %s %lld %lld %lld; pass starts %llu, with even c %llu; smallest c at a pass start after phase 1000: %lld (phase %llu) (%lds)\n", i, ps ? "PS" : "Q", a, m, c, npass, neven, minc, minc_at, (long)(time(0) - t0));
    return 0;
}
