/* Exhaustive 2-adic refinement from block states  G1, B r, W R  (width w).
   A residue class of (r, R, w) mod 2^k is 'settled' when 3 random large completions give the same cascade length;
   unsettled classes are split into 8 at the next level. Reports per level: settled max length, unsettled count. */
#include "model_core.h"
#include <string.h>
static ll pred(ll d) { return (d % 4 == 2) ? (d - 2) / 2 : d / 2 + 4; }
static int run_state(ll r, ll R, ll w0) {
    nm = 0; halted = 0; bad = 0; nend = 0; W = w0;
    add('G', 1); add('B', r); add('W', R);
    int L = 0;
    for (int rd = 0; rd < 400; rd++) {
        do_round();
        if (halted) return 1000;
        if (bad) return -1;
        int alive = 0, ok = 0; for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M' && P[i] == W - 2) ok = 1; }
        L = nend > 0 ? 1 : 0; for (int i = 1; i < nend; i++) { if (endd[i] == pred(endd[i-1])) L++; else return L; }
        if (alive == 2 && ok) return L;
    }
    return L;
}
static unsigned long long rs = 0x13198A2E03707344ULL;
static unsigned long long rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int SB = 56;
static int eval_lift(ll r0, ll R0, ll w0, int k, int t) {
    ll M = 1LL << k;
    int top = SB - k; if (top < 6) top = 6;
    ll w = ((ll)(rnd64() >> 8) % (1LL << top) + (1LL << top)) * M + w0;
    ll D = ((ll)(rnd64() >> 8) % (1LL << (top - 2)) + (1LL << (top - 2))) * M;
    ll R = ((w - D) / M) * M + R0;
    ll r = ((w / (3 + t)) / M) * M + r0;
    return run_state(r, R, w);
}
typedef struct { ll r, R, w; } Cl;
int main(int argc, char **argv) {
    int K = atoi(argv[1]); ll cap = atoll(argv[2]);
    Cl *cur = malloc(sizeof(Cl) * 64); int nc = 0;
    for (ll r = 0; r < 8; r += 2) for (ll R = 1; R < 8; R += 2) for (ll w = 0; w < 8; w += 2) { cur[nc].r = r; cur[nc].R = R; cur[nc].w = w; nc++; }
    int settled_max = 0; long long hist[64] = {0};
    for (int k = 3; k < K && nc > 0; k++) {
        Cl *nx = malloc(sizeof(Cl) * (size_t)nc * 8); long long nn = 0; ll M = 1LL << k;
        long long settled_here = 0;
        for (int i = 0; i < nc; i++) for (int c = 0; c < 8; c++) {
            Cl s = cur[i]; s.r += (c & 1) ? M : 0; s.R += (c & 2) ? M : 0; s.w += (c & 4) ? M : 0;
            int a = eval_lift(s.r, s.R, s.w, k + 1, 0), b = eval_lift(s.r, s.R, s.w, k + 1, 1), d = eval_lift(s.r, s.R, s.w, k + 1, 2);
            if (a == b && b == d) { settled_here++; if (a >= 0 && a < 64) hist[a]++; if (a > settled_max) settled_max = a; }
            else if (nn < cap) nx[nn++] = s;
        }
        free(cur); cur = nx; nc = (int)nn;
        printf("digits %2d: settled so far max %d; unsettled classes carried on: %lld%s\n", k + 1, settled_max, nn, nn >= cap ? " (capped)" : "");
        fflush(stdout);
    }
    printf("settled lengths:"); for (int i = 0; i < 64; i++) if (hist[i]) printf(" %d:%lld", i, hist[i]); printf("\n");
}
