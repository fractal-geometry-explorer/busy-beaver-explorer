/* tokrun: the tape of a run from blank tape as words, at the moments the head extends the visited cells.
 *
 *   tokrun MACHINE MAX_STEPS WORDS [SIDES [K]]
 *
 * WORDS names words of cells, `a=10,b=110`.  Each time the head extends the visited cells on the side other than the
 * last extension's, and that side is in SIDES (L, R or LR, default LR), the tape between the visited extremes is read
 * from the left, longest word first, run-length coded, a cell no word matches printed as itself, in one line
 * "STEPS L|R WIDTH STATE tokens" (WIDTH = hi - lo), at most K lines (default 200).  A halt prints "STEPS HALT".
 * The same output as `python3 -m bbtools.explore tokens` (tools/tests/test_tools.py compares them), for runs of
 * billions of steps.  Steps follow the bbchallenge count.
 */
#include "tm.h"

#define MAXW 16
static int nw, wl[MAXW]; static char wn[MAXW][16]; static unsigned char wc[MAXW][64];

static void flush(FILE *f, const char *tok, long long k, int *first) {
    if (!tok[0]) return;
    fprintf(f, *first ? "%s" : " %s", tok);
    if (k > 1) fprintf(f, "^%lld", k);
    *first = 0;
}

static void print_tokens(const tm_tape *t, FILE *f) {
    char cur[16] = "", tok[16]; long long k = 0; int first = 1;
    long long p = t->lo;
    while (p <= t->hi) {
        int m = -1;
        for (int i = 0; i < nw && m < 0; i++) {
            if (p + wl[i] - 1 > t->hi) continue;
            int ok = 1;
            for (int j = 0; j < wl[i] && ok; j++) ok = tm_get(t, p + j) == wc[i][j];
            if (ok) m = i;
        }
        if (m >= 0) { strcpy(tok, wn[m]); p += wl[m]; } else { tok[0] = (char)('0' + tm_get(t, p)); tok[1] = 0; p++; }
        if (!strcmp(tok, cur)) k++; else { flush(f, cur, k, &first); strcpy(cur, tok); k = 1; }
    }
    flush(f, cur, k, &first);
    fputc('\n', f);
}

static int parse_words(const char *spec) {
    char buf[1024]; strncpy(buf, spec, sizeof buf - 1); buf[sizeof buf - 1] = 0;
    for (char *it = strtok(buf, ","); it; it = strtok(NULL, ",")) {
        char *eq = strchr(it, '=');
        if (!eq || eq == it || nw == MAXW || eq - it >= 16 || strlen(eq + 1) == 0 || strlen(eq + 1) > 64) return -1;
        if (eq - it == 1 && (it[0] == '0' || it[0] == '1')) return -1;
        memcpy(wn[nw], it, (size_t)(eq - it)); wn[nw][eq - it] = 0;
        wl[nw] = (int)strlen(eq + 1);
        for (int j = 0; j < wl[nw]; j++) { if (eq[1 + j] != '0' && eq[1 + j] != '1') return -1; wc[nw][j] = (unsigned char)(eq[1 + j] - '0'); }
        nw++;
    }
    /* longest first, stable (insertion sort) */
    for (int i = 1; i < nw; i++)
        for (int j = i; j > 0 && wl[j] > wl[j - 1]; j--) {
            int l = wl[j]; wl[j] = wl[j - 1]; wl[j - 1] = l;
            char n[16]; strcpy(n, wn[j]); strcpy(wn[j], wn[j - 1]); strcpy(wn[j - 1], n);
            unsigned char c[64]; memcpy(c, wc[j], 64); memcpy(wc[j], wc[j - 1], 64); memcpy(wc[j - 1], c, 64);
        }
    return nw ? 0 : -1;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: tokrun MACHINE MAX_STEPS WORDS [SIDES [K]]\n"); return 1; }
    tm_machine m;
    if (tm_parse(argv[1], &m)) { fprintf(stderr, "bad machine %s\n", argv[1]); return 1; }
    if (parse_words(argv[3])) { fprintf(stderr, "bad words %s\n", argv[3]); return 1; }
    long long max = atoll(argv[2]);
    const char *sides = argc > 4 ? argv[4] : "LR";
    long long kmax = argc > 5 ? atoll(argv[5]) : 200, lines = 0, k = 0;
    tm_tape t; tm_tape_init(&t, 1 << 16);
    int st = 0; char last = 0;
    while (k < max && lines < kmax) {
        long long lo = t.lo, hi = t.hi;
        k++;
        if (!tm_step(&m, &t, &st)) { printf("%lld HALT\n", k); break; }
        char side = t.lo < lo ? 'L' : t.hi > hi ? 'R' : 0;
        if (side && side != last) {
            last = side;
            if (strchr(sides, side)) {
                printf("%lld %c %lld %c ", k, side, t.hi - t.lo, 'A' + st);
                print_tokens(&t, stdout);
                lines++;
            }
        }
    }
    tm_tape_free(&t);
    return 0;
}
