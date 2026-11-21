/* tailsim MACHINE MAXSTEPS [SNAP [ZMIN]] : the concrete part of a round of 1RB---_1LC0LC_1RD1LB_1LE1RD_0LA1LF_1LD0RF.
   stdin: "STATE HEAD CELLS" (CELLS a 0/1 string, HEAD an index into it, blank tape to the right of CELLS).
   Runs until the head moves left of cell 0 (the cut), a halt, or MAXSTEPS steps.
   With ZMIN > 0: also stops at a round start in front of a blank stretch (state B, at least ZMIN 0s on the left
   inside CELLS, 0 1^7 0 from the head), output "inner STEPS STATE HEAD CELLS".
   With SNAP > 0: also prints "snap STEPS STATE HEAD CELLS" every SNAP steps (for inspection).
   stdout: "exit STEPS STATE CELLS" (head now at -1), "halt STEPS STATE HEAD" or "limit STEPS STATE HEAD CELLS". */
#include "../../../tools/c/tm.h"
int main(int argc, char **argv) {
    tm_machine m; tm_parse(argv[1], &m); long long max = (long long)atof(argv[2]);
    char st_c; long long head; static char buf[1 << 26];
    if (scanf(" %c %lld %s", &st_c, &head, buf) != 3) return 2;
    long long n = strlen(buf), cap = 2 * n + (1 << 20);
    unsigned char *c = calloc(cap, 1); for (long long i = 0; i < n; i++) c[i] = buf[i] - '0';
    int st = st_c - 'A'; long long hi = n - 1, k = 0;
    long long snap = argc > 3 ? (long long)atof(argv[3]) : 0;
    /* inner round starts: state B, at least 64 zeros on the left, 0 1^7 0 from the head; with VIS set, print them
       ("vis STEPS HEAD ZEROS" and the 40 cells from the head) */
    long long zmin = argc > 4 ? atoll(argv[4]) : 0;
    int vis = getenv("VIS") != NULL; static const char pb[] = "011111110"; long long nvis = 0;
    while (k < max) {
        if (head < 0) break;
        if (snap && k % snap == 0 && k) {
            printf("snap %lld %c %lld ", k, 'A' + st, head);
            for (long long i = 0; i <= hi; i++) putchar('0' + c[i]);
            putchar('\n'); fflush(stdout);
        }
        if (head >= cap - 1) { long long nc = 2 * cap; c = realloc(c, nc); memset(c + cap, 0, nc - cap); cap = nc; }
        if (zmin && k && st == 1 && head >= zmin && c[head] == 0 && head + 9 <= hi + 1) {
            int ok = 1;
            for (int i = 0; i < 9 && ok; i++) if (c[head + i] != pb[i] - '0') ok = 0;
            for (long long i = 1; i <= zmin && ok; i++) if (c[head - i]) ok = 0;
            if (ok) {
                long long n2 = hi + 1; while (n2 > 0 && c[n2 - 1] == 0) n2--;
                printf("inner %lld %c %lld ", k, 'A' + st, head);
                for (long long i = 0; i < n2; i++) putchar('0' + c[i]);
                putchar('\n'); return 0;
            }
        }
        if (vis && st == 1 && head >= 64 && c[head] == 0) {
            int ok = 1;
            for (int i = 0; i < 9 && ok; i++) if (c[head + i] != pb[i] - '0') ok = 0;
            for (int i = 1; i <= 64 && ok; i++) if (c[head - i]) ok = 0;
            if (ok) {
                long long z = 0; while (head - z - 1 >= 0 && !c[head - z - 1]) z++;
                if ((nvis++ & 1023) == 0) { printf("vis %lld %lld %lld ", k, head, z); for (int i = 0; i < 60; i++) putchar('0' + c[head + i]); putchar('\n'); fflush(stdout); }
            }
        }
        int y = c[head], s = m.s[st][y];
        if (s < 0) { printf("halt %lld %c %lld\n", k + 1, 'A' + st, head); return 0; }
        c[head] = m.w[st][y]; head += m.d[st][y]; st = s; k++;
        if (head > hi) hi = head;
    }
    if (hi >= n) n = hi + 1;
    while (n > 0 && c[n - 1] == 0) n--;
    printf("%s %lld %c %lld ", head < 0 ? "exit" : "limit", k, 'A' + st, head);
    for (long long i = 0; i < n; i++) putchar('0' + c[i]);
    putchar('\n');
    return 0;
}
