/* Beam search over block states  G1, B r, W R  (width w) instead of over n: fix one more binary digit of each of
   r, R, w per level; score a partial state by the cascade length of random completions (min, then average).
   Answers: does the cascade system itself allow much longer cascades from some configuration? */
#include "model_core.h"
#include <string.h>
static ll pred(ll d) { return (d % 4 == 2) ? (d - 2) / 2 : d / 2 + 4; }
static int run_state(ll r, ll R, ll w0) {
    nm = 0; halted = 0; bad = 0; nend = 0; W = w0;
    add('G', 1); add('B', r); add('W', R);
    int L = 0;
    for (int rd = 0; rd < 400; rd++) {
        do_round();
        if (halted) return 100 + L;              /* a carry hit a block inside the model: flag it */
        if (bad) return L;
        int alive = 0, ok = 0; for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M' && P[i] == W - 2) ok = 1; }
        L = nend > 0 ? 1 : 0; for (int i = 1; i < nend; i++) { if (endd[i] == pred(endd[i-1])) L++; else return L; }
        if (alive == 2 && ok) return L;
    }
    return L;
}
static unsigned long long rs = 0x243F6A8885A308D3ULL;
static unsigned long long rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
typedef struct { ll r, R, w; int mn; double avg; } St;
static int cmp(const void *a, const void *b) { const St *x = a, *y = b;
    if (x->mn != y->mn) return y->mn - x->mn; if (x->avg != y->avg) return y->avg > x->avg ? 1 : -1; return 0; }
int NT, SB;
static void score(St *s, int k, int *bestL) {
    int mn = 1000; double sum = 0; ll M = 1LL << k;
    for (int t = 0; t < NT; t++) {
        ll w = ((ll)(rnd64() >> 20) % (1LL << (SB - k)) + (1LL << (SB - k))) * M + s->w;      /* w about 2^(SB+1) */
        ll D = ((ll)(rnd64() >> 20) % (1LL << (SB - 2 - k)) + (1LL << (SB - 2 - k))) * M;       /* D about w/4..w/2 */
        ll R = ((w - D) / M) * M + s->R;
        ll r = ((w / 3) / M) * M + s->r;
        int L = run_state(r, R, w); if (L > *bestL) *bestL = L; if (L < mn) mn = L; sum += L;
    }
    s->mn = mn; s->avg = sum / NT;
}
int main(int argc, char **argv) {
    SB = atoi(argv[1]); int B = atoi(argv[2]); NT = atoi(argv[3]); int K = atoi(argv[4]);
    St *beam = malloc(sizeof(St) * (size_t)B * 8 + 1000); int nb = 0; int bestL = 0;
    int k0 = 3; ll M0 = 1LL << k0;
    for (ll r = 0; r < M0; r += 2) for (ll R = 1; R < M0; R += 2) for (ll w = 0; w < M0; w += 2) {
        beam[nb].r = r; beam[nb].R = R; beam[nb].w = w; score(&beam[nb], k0, &bestL); nb++; }
    qsort(beam, nb, sizeof(St), cmp); if (nb > B) nb = B;
    for (int k = k0; k < K; k++) {
        St *nx = malloc(sizeof(St) * (size_t)nb * 8); int nn = 0; ll M = 1LL << k;
        for (int i = 0; i < nb; i++) for (int c = 0; c < 8; c++) {
            St s = beam[i]; s.r += (c & 1) ? M : 0; s.R += (c & 2) ? M : 0; s.w += (c & 4) ? M : 0;
            score(&s, k + 1, &bestL); nx[nn++] = s; }
        qsort(nx, nn, sizeof(St), cmp); if (nn > B) nn = B;
        memcpy(beam, nx, sizeof(St) * nn); nb = nn; free(nx);
        printf("digits %2d: guaranteed cascade %2d (avg %.2f); longest seen %d\n", k + 1, beam[0].mn, beam[0].avg, bestL); fflush(stdout);
    }
}
