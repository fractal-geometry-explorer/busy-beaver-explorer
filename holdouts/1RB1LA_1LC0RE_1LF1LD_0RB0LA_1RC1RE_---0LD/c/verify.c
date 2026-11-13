/* verify: run Space Needle from blank tape and check the macro rules of lean/Macro.lean against it.
 *
 *   verify MAX_STEPS
 *
 * Every time the head is in state A on a 0 with only 0s to its left, the tape is tested for the shape
 * 0^inf A>0 1^b 0 0 1^c 0^inf.  The sequence of such configurations must be exactly the orbit of (3, 1) under
 * mxdys's map g, reached at step 45 and then once per application of g.  Prints each (step, b, c) and a summary;
 * exits 1 on any mismatch. */
#include "../../../tools/c/tm.h"

static void g(long long *b, long long *c) {
    if (*b == 0) { *b = *c + 2; *c = 1; }
    else if (*b % 2 == 0) { long long k = (*b - 2) / 2; *b = 5 * k + *c + 7; *c = 1; }
    else { long long k = (*b - 3) / 2; *c = k + *c + 4; *b = k; }
}

int main(int argc, char **argv) {
    long long max = argc > 1 ? atoll(argv[1]) : 1000000000LL;
    tm_machine m; tm_parse("1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD", &m);
    tm_tape t; tm_tape_init(&t, 1 << 20);
    int st = 0; long long k = 0, nx = 0, eb = 3, ec = 1, bad = 0;
    while (k < max) {
        k++;
        if (!tm_step(&m, &t, &st)) { printf("halted at step %lld\n", k); return 1; }
        if (st != 0 || tm_get(&t, t.head) != 0) continue;
        long long p = t.head - 1;
        while (p >= t.lo && tm_get(&t, p) == 0) p--;
        if (p >= t.lo) continue;                      /* a 1 to the left */
        long long q = t.head + 1, b = 0, c = 0;
        while (tm_get(&t, q) == 1) { b++; q++; }
        if (tm_get(&t, q) || tm_get(&t, q + 1)) continue;
        q += 2;
        while (tm_get(&t, q) == 1) { c++; q++; }
        if (c == 0) continue;
        long long r = q; int rest = 0;
        for (; r <= t.hi; r++) if (tm_get(&t, r)) { rest = 1; break; }
        if (rest) continue;
        if (b == 0 && c == 1 && nx == 0) continue;     /* step 10: (0, 1) before (3, 1) */
        if (nx == 0 && k != 45) { printf("first X at step %lld, expected 45\n", k); bad = 1; }
        if (b != eb || c != ec) { printf("MISMATCH at step %lld: (%lld, %lld), expected (%lld, %lld)\n", k, b, c, eb, ec); bad = 1; eb = b; ec = c; }
        printf("%lld %lld %lld\n", k, b, c);
        nx++;
        g(&eb, &ec);
    }
    printf("summary: %lld steps, %lld configurations X(b,c), all as predicted: %s\n", k, nx, bad ? "NO" : "yes");
    return bad;
}
