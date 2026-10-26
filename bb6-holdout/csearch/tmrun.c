/* Direct simulation of 1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE from a given tape (string of 0/1), head cell and state.
   Reports a halt, or each clean tape 0^inf A>1 1 (10)^n 1 1 0^inf reached (checked whenever the head is in state A at
   the leftmost 1). Usage: tmrun tapefile head state maxsteps */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long long ll;
/* table[state][symbol] = (write, move(+1 R, -1 L), next) ; next -1 halt */
static const int WR[6][2] = {{1,0},{1,0},{1,1},{1,0},{0,0},{0,1}};
static const int MV[6][2] = {{1,1},{-1,1},{-1,-1},{-1,0},{1,-1},{-1,1}};
static const int NX[6][2] = {{1,4},{2,0},{0,3},{0,-1},{5,1},{3,4}};
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); static char buf[1 << 24]; int n = fread(buf, 1, sizeof buf - 1, f); fclose(f);
    ll head0 = atoll(argv[2]); int st = argv[3][0] - 'A'; ll maxsteps = atoll(argv[4]);
    ll MARGIN = 1 << 20; ll L = n + 2 * MARGIN; unsigned char *tape = calloc(L, 1);
    int len = 0; for (int i = 0; i < n; i++) if (buf[i] == '0' || buf[i] == '1') tape[MARGIN + len++] = buf[i] - '0';
    ll h = MARGIN + head0; ll steps = 0; ll lo = MARGIN, hi = MARGIN + len - 1; int cleans = 0;
    while (steps < maxsteps) {
        int sym = tape[h];
        if (st == 0 && sym == 1) {      /* possible clean tape: leftmost 1 at h? */
            int left_blank = 1; for (ll i = lo; i < h; i++) if (tape[i]) { left_blank = 0; break; }
            if (left_blank && tape[h + 1] == 1) {
                ll i = h + 2; ll pairs = 0; while (tape[i] == 1 && tape[i + 1] == 0) { pairs++; i += 2; }
                if (tape[i] == 1 && tape[i + 1] == 1) { int rb = 1; for (ll j = i + 2; j <= hi + 2; j++) if (tape[j]) { rb = 0; break; }
                    if (rb) { printf("clean tape n = %lld at step %lld\n", pairs, steps); fflush(stdout); if (++cleans >= 2) return 0; } }
            }
        }
        if (st == 4 && getenv("TMROUNDS")) {      /* round start: 1 0 0 E>0 at the left end */
            ll f1 = lo; while (f1 < h && !tape[f1]) f1++;
            if (f1 == h - 3 && tape[f1] == 1 && !tape[f1 + 1] && !tape[f1 + 2] && !tape[h]) {
                ll l1 = hi + 2; while (l1 > f1 && !tape[l1]) l1--;
                printf("round start step %lld width %lld:", steps, l1 - f1 + 1);
                ll i = f1; int shown = 0;
                while (i <= l1 && shown < 12) { ll j = i; while (j + 1 <= l1 && tape[j + 1] == tape[i]) j++; ll ln = j - i + 1;
                    if (ln >= 2) { const char *t = tape[i] ? (ln == 2 ? "M" : ln == 3 ? "B" : "1+") : (ln == 2 ? "W" : ln == 3 ? "G" : "0+"); printf(" %s%lld", t, i - f1); if (ln > 3) printf("(%lld)", ln); shown++; }
                    i = j + 1; }
                printf("\n");
            }
        }
        int nx = NX[st][sym];
        if (nx < 0) { printf("HALT at step %lld, head %lld (relative %lld)\n", steps, h - MARGIN, h - lo);
            ll f1 = lo; while (!tape[f1]) f1++;
            printf("cells %lld..%lld relative to the leftmost 1 (head marked [ ]):\n", h - f1 - 30, h - f1 + 12);
            for (ll i = h - 30; i <= h + 12; i++) { if (i == h) printf("[%d]", tape[i]); else printf("%d", tape[i]); } printf("\n"); return 0; }
        tape[h] = WR[st][sym]; h += MV[st][sym]; st = nx; steps++;
        if (h < lo) lo = h; if (h > hi) hi = h;
        if (h <= 1 || h >= L - 2) { printf("ran off the buffer\n"); return 1; }
    }
    printf("no halt within %lld steps\n", maxsteps);
}
