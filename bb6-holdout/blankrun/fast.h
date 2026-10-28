/* engine.h, rearranged for speed (same rules, same checks, same results; checked against engine.h in simtest and on
   the whole run to width 2^32).  Differences: the marks are one array of (position, type) with free room at both ends,
   so the gap that every round start adds at cell 1 is inserted in O(1); positions are kept relative to an offset that
   grows by 2 or 4 at each round end instead of moving every mark; W below is the width relative to that offset too.
   Real position of mark i: MP(i) + off; real width: W + off. */
#include <stdint.h>
#include <string.h>
typedef int64_t ll;
enum { tG = 0, tM = 1, tW = 2, tB = 3 };
typedef struct { ll p; ll t; } Mk;
#define CAP 512
static Mk buf[CAP]; static int b0 = CAP / 2, nm; static ll W, off;
#define MP(i) buf[b0 + (i)].p
#define MT(i) buf[b0 + (i)].t
static int halted, bad;
static long long tw_canon;
#define MAXEND 4096
static ll endd[MAXEND]; static int endround[MAXEND]; static int nend; static int cur_round;
static const int MLEN[4] = {3, 2, 2, 3};

static void recenter(void) {
    int nb = (CAP - nm) / 2; memmove(&buf[nb], &buf[b0], (size_t)nm * sizeof(Mk)); b0 = nb;
}
static inline void del_at(int i) {
    if (2 * i < nm) { memmove(&buf[b0 + 1], &buf[b0], (size_t)i * sizeof(Mk)); b0++; }
    else memmove(&buf[b0 + i], &buf[b0 + i + 1], (size_t)(nm - i - 1) * sizeof(Mk));
    nm--;
}
static inline void ins_at(int i, int t, ll p) {
    if (nm >= CAP / 2 - 2) { bad = 9; return; }
    if (b0 < 1 || b0 + nm >= CAP - 1) recenter();
    if (2 * i < nm) { memmove(&buf[b0 - 1], &buf[b0], (size_t)i * sizeof(Mk)); b0--; }
    else memmove(&buf[b0 + i + 1], &buf[b0 + i], (size_t)(nm - i) * sizeof(Mk));
    buf[b0 + i].p = p; buf[b0 + i].t = t; nm++;
}
static inline ll mend(int i) { return MP(i) + MLEN[MT(i)]; }
static inline int wall_free(ll w, int i) { return i > 0 ? mend(i - 1) < w : 1 <= w + off; }
static inline int strict_after(ll q, int k) { return k < nm ? q < MP(k) : q < W; }
static inline int free_at(ll q, int k) { return k < nm ? q < MP(k) : q <= W; }

static int packet_back(int k) {
    int b = k - 1; ll y = 0; int crossed = 0;
    while (b >= 0 && MT(b) == tM) { if (crossed && MP(b) + 3 > y) { bad = 11; return -1; } y = MP(b); crossed = 1; b--; }
    if (b < 0) return -1;
    int t = (int)MT(b);
    if (t == tB) { halted = 1; return -1; }
    if (t == tG) { if (crossed && MP(b) + 3 >= y) { bad = 12; return -1; } MP(b) += 2; return b; }
    ll q = MP(b);
    if ((crossed && q + 2 >= y) || !wall_free(q, b)) { bad = 13; return -1; }
    MT(b) = tM; MP(b) = q - 1; ins_at(b + 1, tG, q + 1); return b + 1;
}
static int shift_from(int k) {
    if (k >= nm) { W += 2; ins_at(nm, tM, W - 2); return packet_back(nm - 1); }
    switch (MT(k)) {
    case tM: if (!free_at(MP(k) + 2, k + 1)) { bad = 14; return -1; } MT(k) = tG; return k;
    case tW: if (!strict_after(MP(k) + 2, k + 1)) { bad = 15; return -1; } MT(k) = tB; return packet_back(k);
    case tB:
        if (k == nm - 1 && MP(k) + 3 >= W) {
            if (MP(k) + 3 > W) { bad = 10; return -1; }
            tw_canon++; W -= 1; del_at(k); return packet_back(k);
        }
        if (!strict_after(MP(k) + 3, k + 1)) { bad = 16; return -1; }
        MT(k) = tW; MP(k) += 2; return packet_back(k);
    }
    bad = 2; return -1;
}
static void do_round(void) {
    int gi = 0;
    while (gi >= 0) {
        ll g = MP(gi); int m = gi + 1;
        if (m >= nm) { del_at(gi); W += 3; ins_at(nm, tM, W - 2); gi = packet_back(nm - 1); continue; }
        int t = (int)MT(m);
        if (t == tM) {
            ll d = MP(m) - g - 3;
            if (d < 0 || (d & 1)) { bad = 3; return; }
            if (m == nm - 1 && nend < MAXEND) { endround[nend] = cur_round; endd[nend++] = d; }
            if ((d & 3) == 0) {
                if (d == 0 && !wall_free(g, gi)) { bad = 17; return; }
                MT(gi) = tM; MP(gi) = g + d / 2 - 1; MT(m) = tG; MP(m) = g + d / 2 + 1; gi = m;
            } else {
                if (d == 2 && !wall_free(g, gi) && MT(gi - 1) != tM && MT(gi - 1) != tB) { bad = 18; return; }
                del_at(gi); MT(gi) = tW; MP(gi) = g + d / 2 + 3; gi = packet_back(gi);
            }
        } else if (t == tW) {
            del_at(m); del_at(gi); gi = shift_from(gi);
        } else if (t == tB) {
            if (MP(m) < g + 5) { bad = 19; return; }
            MT(m) = tW; MP(m) -= 1; gi = shift_from(m + 1);
        } else { bad = 4; return; }
        if (bad || halted) return;
    }
    if (bad || halted) return;
    ll extra = 2;
    if (nm > 0 && MT(0) == tM && MP(0) + off == 0) { MT(0) = tW; MP(0) = 1 - off; extra = 4; }
    off += extra;                      /* every real position and the real width grow by extra */
    ins_at(0, tG, 1 - off);
}
/* the real width, and setting up a round start from real positions */
static inline ll realW(void) { return W + off; }
static inline ll realP(int i) { return MP(i) + off; }
static void set_start(ll w) { nm = 0; b0 = CAP / 2; off = 0; W = w; }
static void add_mark(int t, ll p) { ins_at(nm, t, p - off); }
