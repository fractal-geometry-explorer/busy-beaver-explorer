/* triage: a first look at a machine's run from blank tape, as one JSON line.
 *
 *   triage MACHINE MAX_STEPS [SNAP]
 *
 * Runs up to MAX_STEPS steps (bbchallenge count) and reports, at every power of two of steps, [steps, cells visited left
 * of the start, cells visited right of it, 1s, head's offset from the left end]; the step of every new leftmost and rightmost cell (the
 * last 64 of each side, and how many there were); and the tape (run-length coded, cut to SNAP characters, default
 * 400) at the last 4 records of each side. bbtools.triage reads this to sort machines by the shape of their growth.
 */
#include "tm.h"

#define KEEP 64
typedef struct { long long n, t[KEEP]; } recs;

static void rec_add(recs *r, long long k) { r->t[r->n % KEEP] = k; r->n++; }

static void rec_print(const char *name, recs *r) {
    printf("\"%s_n\":%lld,\"%s\":[", name, r->n, name);
    long long a = r->n > KEEP ? r->n - KEEP : 0;
    for (long long i = a; i < r->n; i++) printf("%s%lld", i > a ? "," : "", r->t[i % KEEP]);
    printf("],");
}

static char snapbuf[2][4][4096];
static long long snapstep[2][4];
static int snapn[2];

static void snap(const tm_machine *m, tm_tape *t, int st, int side, long long k, int lim) {
    memset(snapbuf[side][snapn[side] % 4], 0, 4096);
    FILE *f = fmemopen(snapbuf[side][snapn[side] % 4], (size_t)(lim < 4000 ? lim : 4000), "w");
    tm_print(m, t, st, f);
    fclose(f);
    char *s = snapbuf[side][snapn[side] % 4];
    for (char *p = s; *p; p++) if (*p == '\n' || *p == '"') *p = ' ';
    snapstep[side][snapn[side] % 4] = k;
    snapn[side]++;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: triage MACHINE MAX_STEPS [SNAP]\n"); return 1; }
    tm_machine m;
    if (tm_parse(argv[1], &m)) { fprintf(stderr, "bad machine %s\n", argv[1]); return 1; }
    long long max = atoll(argv[2]);
    int lim = argc > 3 ? atoi(argv[3]) : 400;
    tm_tape t; tm_tape_init(&t, 1 << 16);
    int st = 0, halted = 0;
    long long k = 0, next = 1;
    recs L = {0}, R = {0};
    printf("{\"machine\":\"%s\",\"cp\":[", argv[1]);
    int firstcp = 1;
    long long lastsnap[2] = {0, 0};
    while (k < max) {
        long long lo = t.lo, hi = t.hi;
        k++;
        if (!tm_step(&m, &t, &st)) { halted = 1; break; }
        if (t.lo < lo) { rec_add(&L, k); if (k > max / 2 && k - lastsnap[0] > max / 64) { snap(&m, &t, st, 0, k, lim); lastsnap[0] = k; } }
        if (t.hi > hi) { rec_add(&R, k); if (k > max / 2 && k - lastsnap[1] > max / 64) { snap(&m, &t, st, 1, k, lim); lastsnap[1] = k; } }
        if (k == next) {
            printf("%s[%lld,%lld,%lld,%lld,%lld]", firstcp ? "" : ",", k, -t.lo, t.hi, tm_ones(&t), t.head - t.lo);
            firstcp = 0; next *= 2;
        }
    }
    printf("],");
    rec_print("left", &L);
    rec_print("right", &R);
    for (int side = 0; side < 2; side++) {
        printf("\"snap_%s\":[", side ? "right" : "left");
        int a = snapn[side] > 4 ? snapn[side] - 4 : 0;
        for (int i = a; i < snapn[side]; i++)
            printf("%s[%lld,\"%s\"]", i > a ? "," : "", snapstep[side][i % 4], snapbuf[side][i % 4]);
        printf("],");
    }
    char fin[4096];
    memset(fin, 0, sizeof fin);
    FILE *f = fmemopen(fin, (size_t)(lim < 4000 ? lim : 4000), "w");
    tm_print(&m, &t, st, f); fclose(f);
    for (char *p = fin; *p; p++) if (*p == '\n' || *p == '"') *p = ' ';
    printf("\"final\":\"%s\",", fin);
    printf("\"steps\":%lld,\"halted\":%s,\"width\":%lld,\"ones\":%lld,\"state\":\"%c\"}\n", k, halted ? "true" : "false",
           t.hi - t.lo + 1, tm_ones(&t), 'A' + st);
    tm_tape_free(&t);
    return 0;
}
