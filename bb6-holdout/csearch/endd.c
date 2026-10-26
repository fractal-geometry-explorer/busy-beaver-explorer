#include "model_core.h"
static ll pred(ll d) { return (d % 4 == 2) ? (d - 2) / 2 : d / 2 + 4; }
int main(int argc, char **argv) {           /* print the right-end meeting distances of one cycle, marking chain links */
    ll n = atoll(argv[1]); int r; ll nx = cycle(n, &r);
    printf("n=%lld next=%lld rounds=%d meetings=%d:", n, nx, r, nend);
    for (int i = 0; i < nend; i++) printf(" %s%lld", (i > 0 && endd[i] == pred(endd[i-1])) ? "*" : "|", endd[i]);
    printf("\n");
}
