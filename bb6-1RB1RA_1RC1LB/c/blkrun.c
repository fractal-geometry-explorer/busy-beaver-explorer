/* blkrun: the run of 1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB as the block-list macro of py/waves.py (`step`),
 * with exact machine step counts, for runs far beyond direct simulation.
 *
 *   blkrun MACRO_STEPS [EVERY]
 *
 * prints "left K STEP C" each time the wave reaches new tape at the left end (macro step K, machine step STEP, the
 * wave's value C there), "halt K STEP" if the machine halts, a "status" line every EVERY macro steps and an "end"
 * line.  tests/test_waves.py checks its output against waves.py.
 */
#include <stdio.h>
#include <stdlib.h>

typedef long long ll;
typedef __int128 i128;

static void put128(i128 v) {
    char s[64];
    int k = 63;
    s[k] = 0;
    if (v == 0) s[--k] = '0';
    while (v > 0) { s[--k] = (char)('0' + (int)(v % 10)); v /= 10; }
    fputs(s + k, stdout);
}

#define MAXB 100000
static ll b[MAXB], r[MAXB];   /* the blocks left of the wave; the blocks right of it, nearest last */

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: blkrun MACRO_STEPS [EVERY]\n"); return 1; }
    ll K = atoll(argv[1]), every = argc > 2 ? atoll(argv[2]) : 0;
    int n = 0;
    b[n++] = 1; b[n++] = 2;
    i128 T = 17;
    for (ll k = 0; k < K; k++) {
        i128 t;
        if (b[n - 1] == 0) { n--; b[n - 1]++; b[n++] = 2; t = 17; }
        else {
            ll c = b[--n] - 1, x;
            int top = 0;
            r[0] = 1;
            t = 6 + c;
            for (;;) {
                ll y0 = n ? b[n - 1] : 0, j = c / 2;
                if (n == 0) { printf("left %lld ", k); put128(T + t); printf(" %lld\n", c); fflush(stdout); }
                t += (i128)j * (2 * c + 7) - (i128)2 * j * j;
                r[top] += j;
                if (c % 2 == 0) {
                    ll y = y0 + j;
                    if (y >= 2) {
                        if (n) n--;
                        t += y + 3; c = y - 2;
                        if (++top >= MAXB) { fprintf(stderr, "too many blocks\n"); return 2; }
                        r[top] = 1;
                        continue;
                    }
                    if (y == 0) { printf("halt %lld ", k); put128(T + t + 6); printf("\n"); return 0; }
                    if (n) n--;
                    b[n++] = 1; b[n++] = 4; x = r[top] - 1; t += 19;
                } else {
                    if (n) b[n - 1] = y0 + j + 2; else b[n++] = j + 2;
                    x = r[top] + 2; t += 17;
                }
                t += x;
                for (int q = top - 1; q >= 0; q--) t += 2 + r[q];
                if (n + top + 1 >= MAXB) { fprintf(stderr, "too many blocks\n"); return 2; }
                if (top == 0) b[n++] = x;
                else {
                    b[n++] = x + 2;
                    for (int q = top - 1; q >= 1; q--) b[n++] = r[q] + 1;
                    b[n++] = r[0] - 1;
                }
                break;
            }
        }
        T += t;
        if (every && (k + 1) % every == 0) {
            ll s = 0;
            for (int q = 0; q < n; q++) s += b[q];
            printf("status %lld ", k + 1); put128(T); printf(" blocks %d ones %lld\n", n, s); fflush(stdout);
        }
    }
    printf("end %lld ", K); put128(T); printf(" blocks %d\n", n);
    return 0;
}
