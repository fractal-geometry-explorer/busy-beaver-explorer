/* Shared input/output of the simulator drivers (see run.py): read round starts "W t p t p ..." from stdin, run the
   engine's do_round for up to NR rounds, print "R W t p ..." per round, then H (halt), U (no claim) or E, then ".". */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int read_state(char *line, long long *W, char *t, long long *p, int *n) {
    char *s = strtok(line, " \n"); if (!s) return 0; *W = atoll(s); *n = 0;
    while ((s = strtok(NULL, " \n"))) { t[*n] = s[0]; s = strtok(NULL, " \n"); if (!s) return 0; p[(*n)++] = atoll(s); }
    return 1;
}
