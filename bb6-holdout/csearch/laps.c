/* For P = 3*2^k: which residues n mod P does the machine's own trajectory visit in each lap [jP, (j+1)P)?
   Prints, for consecutive laps, how many residues they share. Uses the mark model from model.c. */
#include "model_core.h"
#include <string.h>
int main(int argc, char **argv) {
    int k = atoi(argv[1]); ll limit = atoll(argv[2]); ll P = 3LL << k;
    unsigned char *prev = calloc(P, 1), *cur = calloc(P, 1);
    ll n = 2, lap = 0, cnt = 0, pcnt = 0; int r;
    while (n < limit) {
        ll j = n / P;
        if (j != lap) {
            ll shared = 0; for (ll i = 0; i < P; i++) shared += prev[i] & cur[i];
            if (lap >= 1) printf("lap %lld: %lld visits, %lld shared with lap %lld (%.4f)\n", lap, cnt, shared, lap - 1, pcnt ? (double)shared / pcnt : 0);
            unsigned char *t = prev; prev = cur; cur = t; memset(cur, 0, P); pcnt = cnt; cnt = 0; lap = j;
        }
        cur[n % P] = 1; cnt++;
        n = cycle(n, &r);
    }
    return 0;
}
