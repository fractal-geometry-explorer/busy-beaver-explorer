#include "model_core_r.h"
/* first run of right-end meetings (each next d = pred(previous d)) from block states G 1, B r, W R near fixed geometry */
static ll pred(ll d) { return (d % 4 == 2) ? (d - 2) / 2 : d / 2 + 4; }
int main(int argc, char **argv) {
    long N = atol(argv[1]); unsigned long long s = 0x2545F4914F6CDD1DULL; long long cnt[64] = {0}; long tot = 0;
    for (long t = 0; t < N; t++) {
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll E = (ll)((s >> 14) | (1ULL << 49)) & ~1LL;
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll r = ((ll)(E * 0.3) + (ll)(s >> 34)) & ~1LL;
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; ll D = (E / 200 + (ll)(s >> 34)) | 1;
        ll R = E - D;
        nm = 0; halted = 0; bad = 0; nend = 0; W = E; add('G', 1); add('B', r); add('W', R);
        int L = 0;
        for (int rd = 1; rd < 400; rd++) {
            int ne0 = nend; CUR_RD = rd; do_round(); if (halted || bad) break;
            int br = 0;
            for (int i = ne0; i < nend; i++) { if (i > 0 && endd[i] != pred(endd[i-1])) { br = 1; break; } L++; }
            if (br) break;
            int ok = 0, alive = 0; for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M' && P[i] == W - 2) ok = 1; }
            if (alive == 2 && ok) break;
        }
        if (L > 63) L = 63; cnt[L]++; tot++;
    }
    long long ge = 0; for (int l = 63; l >= 1; l--) { ge += cnt[l]; if (l <= 14 && ge) printf("P(run >= %2d) = %.4e  (%lld)\n", l, (double)ge / tot, ge); }
}
