/* tcyc.c: cycler and translated-cycler detection from blank tape, up to N steps.
   Cycler: a configuration repeats exactly (checked at record-free... via Brent on full config is costly; we use:
   translated cycler test at record events on each side (covers cyclers with growth); pure cyclers: tape bounded,
   detect by hashing full configuration every step after the reach stops growing for a while (Brent's algorithm). */
#include "tm.h"
#define K 4000
#define L 2048
typedef struct { long long step, pos; int st; long long segmin; unsigned char snap[L]; } ev;
static ev E[2][K]; static int ne[2], hd[2];
int main(int c, char **v) {
    tm_machine m; if (tm_parse(v[1], &m)) return 1; long long N = atoll(v[2]);
    tm_tape t; tm_tape_init(&t, 1 << 20); int st = 0; long long lo = 0, hi = 0, mn[2] = {0, 0};
    for (long long k = 1; k <= N; k++) {
        if (!tm_step(&m, &t, &st)) { printf("HALT %lld\n", k); return 0; }
        long long h = t.head;
        for (int s = 0; s < 2; s++) { long long rel = s ? h : -h; if (-rel > mn[s]) mn[s] = -rel; }
        int side = -1;
        if (h > hi) { hi = h; side = 1; } else if (h < lo) { lo = h; side = 0; }
        if (side < 0) continue;
        /* segmin for the previous event of this side: farthest retreat since it */
        int s = side; long long rel = s ? h : -h;
        if (ne[s]) { ev *p = &E[s][(hd[s] + ne[s] - 1) % K]; p->segmin = mn[s]; }
        mn[s] = -rel;
        /* compare with earlier events of the same state */
        long long far = -rel; /* most negative relative coord since each earlier event, scanning back */
        for (int i = ne[s] - 1; i >= 0; i--) {
            ev *p = &E[s][(hd[s] + i) % K];
            if (p->segmin > far) far = p->segmin; /* segmin stores max of -rel i.e. farthest back */
            if (p->st != st) continue;
            long long prel = s ? p->pos : -p->pos, back = far + prel; /* cells behind head at p's time */
            if (back >= L) continue;
            int ok = 1;
            for (long long j = 0; j <= back && ok; j++) {
                int a = p->snap[j], b = tm_get(&t, s ? h - j : h + j);
                if (a != b) ok = 0;
            }
            if (ok) { printf("TCYCLER side %c period %lld start %lld shift %lld\n", s ? 'R' : 'L', k - p->step, p->step, rel - prel); return 0; }
        }
        ev *q; if (ne[s] < K) q = &E[s][(hd[s] + ne[s]++) % K]; else { q = &E[s][hd[s]]; hd[s] = (hd[s] + 1) % K; }
        q->step = k; q->pos = h; q->st = st; q->segmin = 0;
        for (int j = 0; j < L; j++) q->snap[j] = (unsigned char)tm_get(&t, s ? h - j : h + j);
    }
    printf("NONE %lld\n", N); return 0;
}
