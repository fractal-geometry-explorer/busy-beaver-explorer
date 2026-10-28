/* blankrun: the machine's run from blank tape in the mark model (engine.h), cycle by cycle (one clean tape to the
   next), logging every round start with three walls, the right-end meetings and the checkpoints.

   usage: blankrun TARGET_W [N CYCLES ROUNDS]     run until the first clean tape of width >= TARGET_W; with N, start
                                                   from the clean tape n = N (width 2N + 6) as cycle CYCLES after
                                                   ROUNDS rounds (a checkpoint line of an earlier run)
   Output lines (stdout):
     K W n cycles rounds                 a clean tape whose width W is the first >= 2^k, for every k (checkpoints;
                                         W = 2^20 after 294,033 rounds and 2^32 after 1,204,297,272 are the Lean
                                         prefix theorems' values, blank_prefix_kernel and blank_prefix)
     T cycle n r a b c W hmin            a round start G 1, W a, W b, W c of width W after round r of the cycle from
                                         clean tape n; hmin: the cycle's closest end meeting so far, in halvings
                                         log2(W/d) at that meeting (only end meetings before this round start)
     E cycle n n' rounds chain dmin Wd   end of a cycle that had a T line: next clean tape n', rounds, longest
                                         halving chain of end meetings, closest end meeting dmin at width Wd
     H cycle n halvings chain dmin Wd    a new record of the closest end meeting (any cycle)
     Z ...                               periodic status (stderr too)
   The run stops with a message if the model halts or meets a configuration it does not cover. */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include "engine.h"

static ll pred(ll d) { return (d % 4 == 2) ? (d - 2) / 2 : d / 2 + 4; }
#define MAXT 256
static ll ta[MAXT], tb[MAXT], tc[MAXT], tw[MAXT]; static int tr[MAXT]; static double th[MAXT]; static int nt;

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: blankrun TARGET_W [N CYCLES ROUNDS]\n"); return 2; }
    ll target = atoll(argv[1]);
    long long cyc = 0, rounds_total = 0;
    nm = 0;
    if (argc > 4) {
        ll n0 = atoll(argv[2]); cyc = atoll(argv[3]); rounds_total = atoll(argv[4]);
        W = 2 * n0 + 6; ins_at(0, 'G', 1); ins_at(1, 'M', W - 2);
    } else { W = 5; ins_at(0, 'G', 1); }        /* roundStart [] 5: 17 steps from blank tape */
    int k_next = 0; while (k_next < 63 && ((ll)1 << k_next) <= W) k_next++;
    double best_h = 0; long long ntw = 0, ntw_cycles = 0, nps = 0;
    long long chain_hist[64] = {0};
    ll wd_unused = 0; (void)wd_unused;
    for (;;) {
        ll n = (W - 6) / 2;                     /* the clean tape this cycle starts from (n = -1/2 at the blank start) */
        nend = 0; nt = 0; int r = 0;
        ll dmin = -1, wdmin = 0; double hmin = -99;
        for (;;) {
            cur_round = ++r; int ne0 = nend; ll w0 = W;
            do_round(); rounds_total++;
            if (halted || bad) {
                printf("STOP cycle %lld n %lld round %d: %s %d\n", cyc, (long long)n, r, halted ? "halt" : "uncovered", bad);
                fprintf(stderr, "STOP at cycle %lld n %lld round %d: halted %d bad %d\n", cyc, (long long)n, r, halted, bad);
                return 1;
            }
            for (int i = ne0; i < nend; i++) {      /* end meetings of this round (width w0 at the round's start) */
                ll d = endd[i];
                if (dmin < 0 || d < dmin) { dmin = d; wdmin = w0; }
                double h = d > 0 ? log2((double)w0) - log2((double)d) : 99.0;
                if (h > hmin) hmin = h;
            }
            if (nm == 4 && T[1] == 'W' && T[2] == 'W' && T[3] == 'W' && nt < MAXT) {
                ta[nt] = P[1]; tb[nt] = P[2]; tc[nt] = P[3]; tw[nt] = W; tr[nt] = r; th[nt] = hmin; nt++;
            }
            if (nm == 2 && T[1] == 'M' && P[1] == W - 2) break;
            if (r > 100000) { printf("STOP cycle %lld n %lld: no clean tape in 100000 rounds\n", cyc, (long long)n); return 1; }
        }
        cyc++;
        ll n2 = (W - 6) / 2;
        int best = nend > 0 ? 1 : 0, cur = 1;
        for (int i = 1; i < nend; i++) { if (endd[i] == pred(endd[i - 1])) { cur++; if (cur > best) best = cur; } else cur = 1; }
        chain_hist[best < 63 ? best : 63]++;
        if (nt > 0) {
            ntw += nt; ntw_cycles++;
            for (int i = 0; i < nt; i++) {
                printf("T %lld %lld %d %lld %lld %lld %lld %.3f\n", cyc, (long long)n, tr[i], (long long)ta[i], (long long)tb[i],
                       (long long)tc[i], (long long)tw[i], th[i]);
                ll R = tw[i] - tc[i] - 1;
                if ((ta[i] & 1) && !(tb[i] & 1) && !(tw[i] & 1) && !(R & 1) && R >= 2 && ta[i] >= 448 && ta[i] + 448 <= tb[i]
                    && tb[i] + 448 + R + 1 <= tw[i]) nps++;
            }
            printf("E %lld %lld %lld %d %d %lld %lld\n", cyc, (long long)n, (long long)n2, r, best, (long long)dmin, (long long)wdmin);
        }
        if (hmin > best_h + 1e-9 && W > 1000) {
            best_h = hmin;
            printf("H %lld %lld %.4f %d %lld %lld\n", cyc, (long long)n, hmin, best, (long long)dmin, (long long)wdmin);
        }
        while (k_next < 63 && W >= ((ll)1 << k_next)) {
            printf("K %lld %lld %lld %lld\n", (long long)W, (long long)n2, cyc, rounds_total);
            fprintf(stderr, "K 2^%d: W %lld n %lld cycles %lld rounds %lld; three-wall round starts %lld in %lld cycles, pass starts (gaps >= 448) %lld; trailing-wall forms %lld\n",
                    k_next, (long long)W, (long long)n2, cyc, rounds_total, ntw, ntw_cycles, nps, tw_canon);
            printf("Z cycles %lld rounds %lld three-wall %lld in %lld cycles, pass starts %lld, trailing-wall %lld, chains",
                   cyc, rounds_total, ntw, ntw_cycles, nps, tw_canon);
            for (int i = 0; i < 64; i++) if (chain_hist[i]) printf(" %d:%lld", i, chain_hist[i]);
            printf("\n");
            fflush(stdout);
            k_next++;
        }
        if (W >= target) break;
    }
    return 0;
}
