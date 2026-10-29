/* tm.h: a two-symbol Turing machine in the standard text format, and a direct simulator.
 *
 * Header-only; any program that includes it gets
 *   tm_parse(text, &m)          parse "1RB1RA_..." (returns 0, or -1 on a malformed machine); a transition is a
 *                               halt if it is "---" or its next state is not one of the machine's ("1RZ")
 *   tm_tape_init / tm_tape_free a tape that grows on demand at both ends
 *   tm_step(&m, &t, &st)        one transition; returns 0 if it is the halting one, which is not carried out
 *                               (the bbchallenge count calls it a step; the tape stays as it was before it)
 *   tm_run(&m, &t, &st, max)    steps until a halt or max steps; returns the steps made, sets *halted
 *   tm_print(&m, &t, st, f)     the tape between the visited extremes, run-length coded: "1^5 0 C>1 1^2"
 *
 * The cross-check against the Python reference simulator is tools/tests/test_tools.py (machines with known step
 * counts, and random machines compared step by step).
 */
#ifndef TM_H
#define TM_H
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define TM_MAXS 10
typedef struct { int n; signed char w[TM_MAXS][2], d[TM_MAXS][2], s[TM_MAXS][2]; } tm_machine; /* s = -1: halt */
typedef struct { unsigned char *c; long long size, off, head, lo, hi; } tm_tape; /* cell at position p: c[p + off] */

static inline int tm_parse(const char *text, tm_machine *m) {
    int len = (int)strlen(text);
    if ((len + 1) % 7 != 0) return -1;
    m->n = (len + 1) / 7;
    if (m->n < 1 || m->n > TM_MAXS) return -1;
    for (int s = 0; s < m->n; s++) {
        if (s > 0 && text[7 * s - 1] != '_') return -1;
        for (int y = 0; y < 2; y++) {
            const char *t = text + 7 * s + 3 * y;
            if (t[2] == '-' || t[2] - 'A' < 0 || t[2] - 'A' >= m->n) { m->s[s][y] = -1; m->w[s][y] = 0; m->d[s][y] = 0; continue; }
            if ((t[0] != '0' && t[0] != '1') || (t[1] != 'L' && t[1] != 'R')) return -1;
            m->w[s][y] = (signed char)(t[0] - '0'); m->d[s][y] = t[1] == 'R' ? 1 : -1; m->s[s][y] = (signed char)(t[2] - 'A');
        }
    }
    return 0;
}

static inline void tm_tape_init(tm_tape *t, long long size) {
    t->size = size; t->c = (unsigned char *)calloc((size_t)size, 1); t->off = size / 2; t->head = t->lo = t->hi = 0;
    if (!t->c) { fprintf(stderr, "out of memory\n"); exit(2); }
}
static inline void tm_tape_free(tm_tape *t) { free(t->c); t->c = NULL; }

static inline void tm_grow(tm_tape *t) {
    long long n = t->size;
    unsigned char *c = (unsigned char *)calloc((size_t)(3 * n), 1);
    if (!c) { fprintf(stderr, "out of memory\n"); exit(2); }
    memcpy(c + n, t->c, (size_t)n); free(t->c); t->c = c; t->size = 3 * n; t->off += n;
}

static inline int tm_get(const tm_tape *t, long long p) {
    long long i = p + t->off;
    return (i < 0 || i >= t->size) ? 0 : t->c[i];
}

static inline int tm_step(const tm_machine *m, tm_tape *t, int *st) {
    long long i = t->head + t->off;
    if (i < 0 || i >= t->size) { tm_grow(t); i = t->head + t->off; }
    int y = t->c[i], s = m->s[*st][y];
    if (s < 0) return 0;
    t->c[i] = (unsigned char)m->w[*st][y];
    t->head += m->d[*st][y]; *st = s;
    if (t->head < t->lo) t->lo = t->head;
    if (t->head > t->hi) t->hi = t->head;
    return 1;
}

static inline long long tm_run(const tm_machine *m, tm_tape *t, int *st, long long max, int *halted) {
    long long k = 0; *halted = 0;
    while (k < max) { k++; if (!tm_step(m, t, st)) { *halted = 1; break; } }
    return k;
}

static inline long long tm_ones(const tm_tape *t) {
    long long n = 0;
    for (long long p = t->lo; p <= t->hi; p++) n += tm_get(t, p);
    return n;
}

static inline void tm_print(const tm_machine *m, const tm_tape *t, int st, FILE *f) {
    (void)m;
    long long p = t->lo; int first = 1;
    while (p <= t->hi) {
        if (p == t->head) { fprintf(f, "%s%c>%d", first ? "" : " ", 'A' + st, tm_get(t, p)); p++; first = 0; continue; }
        int v = tm_get(t, p); long long q = p;
        while (q <= t->hi && q != t->head && tm_get(t, q) == v) q++;
        if (q - p > 1) fprintf(f, "%s%d^%lld", first ? "" : " ", v, q - p); else fprintf(f, "%s%d", first ? "" : " ", v);
        first = 0; p = q;
    }
    fputc('\n', f);
}
#endif
