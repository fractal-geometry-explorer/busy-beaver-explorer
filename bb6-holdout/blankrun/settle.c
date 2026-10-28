/* settle: for clean tapes n, the depth of n's class in the class tree of the exhaustive check (../csearch/nrefdfs2.c,
   ../csearch/settle.c): the number of low binary digits of n that n's cycle reads.

   In the class n = rho + 2^k j every position is an affine function of j, and a swap/merge test on a distance d is
   decided for the whole class when d's coefficient of j is a multiple of 4; otherwise the class needs the next digit.
   Every position is lambda (2n + 6) + c with lambda dyadic, so d's coefficient at depth k is lambda_d 2^(k+1), and the
   test is decided from depth k = 1 - v2(lambda_d) on.  This program runs n's own cycle on integers (engine.h's rules)
   and carries, for each mark, its coefficient a = lambda 2^(K+1) at the depth K = 120; a test on a distance with
   coefficient a_d is decided from depth K + 2 - v2(a_d).  The depth of n's class is the largest of these over the cycle
   (0 if none).  For a depth below the bit length of n this is the depth at which the exhaustive check settles n's
   class (n follows its class there, by the spare-digit bound j_min <= 1); a depth at or above the bit length means n is
   left open at every depth it has digits for, and the exhaustive check runs it directly.

   usage: settle < list of n      (one per line; other fields after n are ignored)
   output: n depth rounds next_n */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef int64_t ll; typedef __int128 i128;
#define MAXM 120
#define K 120
static char T[MAXM]; static ll P[MAXM]; static i128 A[MAXM]; static int nm; static ll W; static i128 AW;
static int halted, bad, depth;
static int v2(i128 x) { if (x == 0) return 999; if (x < 0) x = -x; int k = 0; while (!(x & 1)) { x >>= 1; k++; } return k; }
static void del_at(int i) {
    memmove(&T[i], &T[i + 1], (size_t)(nm - i - 1)); memmove(&P[i], &P[i + 1], (size_t)(nm - i - 1) * sizeof(ll));
    memmove(&A[i], &A[i + 1], (size_t)(nm - i - 1) * sizeof(i128)); nm--;
}
static void ins_at(int i, char t, ll p, i128 a) {
    if (nm >= MAXM) { bad = 9; return; }
    memmove(&T[i + 1], &T[i], (size_t)(nm - i)); memmove(&P[i + 1], &P[i], (size_t)(nm - i) * sizeof(ll));
    memmove(&A[i + 1], &A[i], (size_t)(nm - i) * sizeof(i128));
    T[i] = t; P[i] = p; A[i] = a; nm++;
}
static int packet_back(int k) {
    int b = k - 1;
    while (b >= 0 && T[b] == 'M') b--;
    if (b < 0) return -1;
    if (T[b] == 'B') { halted = 1; return -1; }
    if (T[b] == 'G') { P[b] += 2; return b; }
    ll q = P[b]; i128 a = A[b]; T[b] = 'M'; P[b] = q - 1; ins_at(b + 1, 'G', q + 1, a); return b + 1;
}
static int shift_from(int k) {
    if (k >= nm) { W += 2; ins_at(nm, 'M', W - 2, AW); return packet_back(nm - 1); }
    switch (T[k]) {
    case 'M': T[k] = 'G'; return k;
    case 'W': T[k] = 'B'; return packet_back(k);
    case 'B':
        if (k == nm - 1 && P[k] + 3 >= W) {
            if (P[k] + 3 > W || A[k] != AW) { bad = 10; return -1; }
            W -= 1; del_at(k); return packet_back(k);
        }
        T[k] = 'W'; P[k] += 2; return packet_back(k);
    }
    bad = 2; return -1;
}
static void need(i128 ad) { if (ad != 0) { int k = K + 2 - v2(ad); if (k > depth) depth = k; } }
static void do_round(void) {
    int gi = 0;
    while (gi >= 0) {
        ll g = P[gi]; i128 ag = A[gi]; int m = gi + 1;
        if (m >= nm) { del_at(gi); W += 3; ins_at(nm, 'M', W - 2, AW); gi = packet_back(nm - 1); continue; }
        char t = T[m];
        if (t == 'M') {
            ll d = P[m] - g - 3; i128 ad = A[m] - ag;
            if (d < 0 || (d & 1)) { bad = 3; return; }
            need(ad);
            if ((d & 3) == 0) { T[gi] = 'M'; P[gi] = g + d / 2 - 1; A[gi] = ag + ad / 2; T[m] = 'G'; P[m] = g + d / 2 + 1; A[m] = ag + ad / 2; gi = m; }
            else { del_at(gi); T[gi] = 'W'; P[gi] = g + d / 2 + 3; A[gi] = ag + ad / 2; gi = packet_back(gi); }
        } else if (t == 'W') { del_at(m); del_at(gi); gi = shift_from(gi); }
        else if (t == 'B') { T[m] = 'W'; P[m] -= 1; gi = shift_from(m + 1); }
        else { bad = 4; return; }
        if (bad || halted) return;
    }
    if (bad || halted) return;
    ll extra = 2;
    if (nm > 0 && T[0] == 'M' && P[0] == 0) { T[0] = 'W'; P[0] = 1; extra = 4; }
    for (int i = 0; i < nm; i++) P[i] += extra;
    W += extra; ins_at(0, 'G', 1, 0);
}
int main(void) {
    char line[512];
    while (fgets(line, sizeof line, stdin)) {
        ll n = atoll(line); if (n <= 0) continue;
        nm = 0; halted = bad = 0; depth = 0; W = 2 * n + 6; AW = (i128)1 << (K + 1);
        ins_at(0, 'G', 1, 0); ins_at(1, 'M', W - 2, AW);
        int r = 0;
        for (;;) {
            do_round(); r++;
            if (halted || bad) { printf("%lld STOP %d %d\n", (long long)n, halted, bad); break; }
            if (nm == 2 && T[1] == 'M' && P[1] == W - 2) { printf("%lld %d %d %lld\n", (long long)n, depth, r, (long long)((W - 6) / 2)); break; }
            if (r > 1000000) { printf("%lld LONG\n", (long long)n); break; }
        }
    }
    return 0;
}
