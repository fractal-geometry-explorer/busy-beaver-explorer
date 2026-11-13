/* direct.c: the plain simulator of tools/c/tm.h, printing the tape at every sweep end the way rl.c does with
   EVERY = 1, for the first group's orientation (the tape grows to the right; a sweep end is the head stepping onto a
   fresh right cell in state E).  Blocks of 0010 are printed as B<count>, other cells literally, zeros at both ends
   left out.  usage: direct MACHINE MAXSTEPS */
#include "../../../tools/c/tm.h"
int main(int argc, char **argv) {
    tm_machine m; tm_parse(argv[1], &m); long long max = atoll(argv[2]);
    tm_tape t; tm_tape_init(&t, 1 << 16); int st = 0; long long k = 0;
    while (k < max) {
        long long ohi = t.hi; k++;
        if (!tm_step(&m, &t, &st)) { printf("halted %lld\n", k); return 0; }
        if (t.head > ohi && st == 4) {
            printf("S %lld", k);
            /* tokens over the visited cells: runs of 0010 and single cells; then drop single 0s at both ends */
            static long long tv[1 << 22]; long long n = 0, p = t.lo;   /* tv: -c for a run of c, else the cell */
            while (p <= t.hi) {
                if (p + 3 <= t.hi && tm_get(&t, p) == 0 && tm_get(&t, p + 1) == 0 && tm_get(&t, p + 2) == 1 && tm_get(&t, p + 3) == 0) {
                    long long c = 0;
                    while (p + 3 <= t.hi && tm_get(&t, p) == 0 && tm_get(&t, p + 1) == 0 && tm_get(&t, p + 2) == 1 && tm_get(&t, p + 3) == 0) { c++; p += 4; }
                    tv[n++] = -c;
                } else tv[n++] = tm_get(&t, p++);
            }
            long long a = 0, b = n - 1; while (a <= b && tv[a] == 0) a++; while (b >= a && tv[b] == 0) b--;
            int inlit = 0;
            for (long long q = a; q <= b; q++) {
                if (tv[q] < 0) { printf(" B%lld", -tv[q]); inlit = 0; }
                else { if (!inlit) { putchar(' '); inlit = 1; } putchar('0' + (int)tv[q]); }
            }
            putchar('\n');
        }
    }
    printf("running %lld\n", k);
    return 0;
}
