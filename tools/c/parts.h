/* parts.h: the output protocol of a search split into parts (tools/c/run_parts.sh runs them, tools/py/merge_parts.py
 * merges them).
 *
 * A part program takes PART NPARTS as its last two arguments, works on its share of the search (parts_owns), and
 * writes lines of these kinds (anything else is a comment the merge ignores):
 *   sum NAME VALUE                summed over the parts
 *   max NAME VALUE [WITNESS...]   the largest over the parts, with the witness of the first part that has it
 *   min NAME VALUE [WITNESS...]   the smallest
 *   event TEXT...                 kept, every one (halts found, anything a person must look at)
 *   done PART NPARTS              written last: a part without it did not finish, and the merge refuses it
 * VALUEs are integers (up to 128 bits in the merge).  The merge writes the same protocol, with "done all N".
 */
#ifndef PARTS_H
#define PARTS_H
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>

static int PART = 0, NPARTS = 1;

/* Read PART NPARTS from the last two arguments when there are more than `fixed` arguments (argv[0] included). */
static inline void parts_args(int argc, char **argv, int fixed) {
    if (argc >= fixed + 2) { PART = atoi(argv[argc - 2]); NPARTS = atoi(argv[argc - 1]); }
    if (NPARTS < 1 || PART < 0 || PART >= NPARTS) { fprintf(stderr, "bad part %d of %d\n", PART, NPARTS); exit(1); }
}

/* Whether this part owns item k of a split level (strided, so parts get mixed work). */
static inline int parts_owns(unsigned long long k) { return (int)(k % (unsigned long long)NPARTS) == PART; }

static inline void parts_sum(const char *name, long long v) { printf("sum %s %lld\n", name, v); }
static inline void parts_max(const char *name, long long v, const char *fmt, ...) {
    printf("max %s %lld", name, v);
    if (fmt) { va_list a; va_start(a, fmt); putchar(' '); vprintf(fmt, a); va_end(a); }
    putchar('\n');
}
static inline void parts_min(const char *name, long long v, const char *fmt, ...) {
    printf("min %s %lld", name, v);
    if (fmt) { va_list a; va_start(a, fmt); putchar(' '); vprintf(fmt, a); va_end(a); }
    putchar('\n');
}
static inline void parts_event(const char *fmt, ...) {
    va_list a; va_start(a, fmt); printf("event "); vprintf(fmt, a); putchar('\n'); va_end(a);
}
static inline void parts_done(void) { printf("done %d %d\n", PART, NPARTS); fflush(stdout); }
#endif
