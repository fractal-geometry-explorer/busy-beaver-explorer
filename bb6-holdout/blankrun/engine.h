/* The mark model of 1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE on integer positions, for following one run fast.

   The rules are those of model_core.h and the fixed engines (../csearch/lined.c, nrefdfs2.c), with the trailing-wall
   fix: a shift that reaches a block ending the tape writes the canonical form (no wall, width W - 1), as roundZ in
   ../lean/BB6/Round.lean does.  The marks sit in an array sorted by position, so "next to the right" and "nearest
   non-marker to the left" are neighbours.  Where roundZ (gapEvent, pktBack, pktLand) leaves a configuration uncovered
   (marks touching where a rule needs room), the run stops with bad != 0 instead of applying a rule outside its
   conditions.

   Coordinates as in ../rec/clean_recurrence.py: cell 0 is the leftmost 1, a round starts with the gap G at cell 1,
   W is the width.  Marks: G gap (3 cells), M marker (2), W wall (2), B block (3). */
#include <stdint.h>
#include <string.h>
typedef int64_t ll;
#define MAXM 120
static char T[MAXM]; static ll P[MAXM]; static int nm; static ll W;
static int halted, bad;
static long long tw_canon;                       /* trailing-wall canonical forms written */
/* end meetings of the current cycle: distance and the round they happen in */
#define MAXEND 4096
static ll endd[MAXEND]; static int endround[MAXEND]; static int nend; static int cur_round;

static inline void del_at(int i) {
    memmove(&T[i], &T[i + 1], (size_t)(nm - i - 1)); memmove(&P[i], &P[i + 1], (size_t)(nm - i - 1) * sizeof(ll)); nm--;
}
static inline void ins_at(int i, char t, ll p) {
    if (nm >= MAXM) { bad = 9; return; }
    memmove(&T[i + 1], &T[i], (size_t)(nm - i)); memmove(&P[i + 1], &P[i], (size_t)(nm - i) * sizeof(ll));
    T[i] = t; P[i] = p; nm++;
}
static inline ll mend(int i) { return P[i] + ((T[i] == 'G' || T[i] == 'B') ? 3 : 2); }   /* first cell after mark i */
/* a stripe cell before position w: the mark left of index i ends before w - 1 (wallFreeB) */
static inline int wall_free(ll w, int i) { return i > 0 ? mend(i - 1) < w : 1 <= w; }
/* strictAfterB / freeAtB: the next mark (index k) or the width lies strictly after q, or at or after q */
static inline int strict_after(ll q, int k) { return k < nm ? q < P[k] : q < W; }
static inline int free_at(ll q, int k) { return k < nm ? q < P[k] : q <= W; }

/* A packet travels left from the marks left of index k, past markers (pktBack, pktLand).  Returns the index of the
   woken gap, or -1 at the left end (the round ends) or on a halt. */
static int packet_back(int k) {
    int b = k - 1; ll y = -1;                    /* y: the last marker crossed */
    while (b >= 0 && T[b] == 'M') { if (y >= 0 && P[b] + 3 > y) { bad = 11; return -1; } y = P[b]; b--; }
    if (b < 0) return -1;
    if (T[b] == 'B') { halted = 1; return -1; }
    if (T[b] == 'G') { if (y >= 0 && P[b] + 3 >= y) { bad = 12; return -1; } P[b] += 2; return b; }
    ll q = P[b];                                 /* a wall at q becomes a marker at q - 1 and a gap at q + 1 */
    if ((y >= 0 && q + 2 >= y) || !wall_free(q, b)) { bad = 13; return -1; }
    T[b] = 'M'; P[b] = q - 1; ins_at(b + 1, 'G', q + 1); return b + 1;
}
/* A shift runs right; k is the index of the first mark to its right (nm if none).  Returns the next active gap. */
static int shift_from(int k) {
    if (k >= nm) { W += 2; ins_at(nm, 'M', W - 2); return packet_back(nm - 1); }
    switch (T[k]) {
    case 'M': if (!free_at(P[k] + 2, k + 1)) { bad = 14; return -1; } T[k] = 'G'; return k;
    case 'W': if (!strict_after(P[k] + 2, k + 1)) { bad = 15; return -1; } T[k] = 'B'; return packet_back(k);
    case 'B':
        if (k == nm - 1 && P[k] + 3 >= W) {
            if (P[k] + 3 > W) { bad = 10; return -1; }
            tw_canon++; W -= 1; del_at(k); return packet_back(k);   /* the block ended the tape: canonical form */
        }
        if (!strict_after(P[k] + 3, k + 1)) { bad = 16; return -1; }
        T[k] = 'W'; P[k] += 2; return packet_back(k);
    }
    bad = 2; return -1;
}
/* One round from a round start (G at index 0, cell 1) to the next (gapEvent until a packet reaches the left end). */
static void do_round(void) {
    int gi = 0;
    while (gi >= 0) {
        ll g = P[gi]; int m = gi + 1;
        if (m >= nm) {                           /* the gap reaches the blank end: a new end marker, a packet */
            del_at(gi); W += 3; ins_at(nm, 'M', W - 2); gi = packet_back(nm - 1); continue;
        }
        char t = T[m];
        if (t == 'M') {
            ll d = P[m] - g - 3;
            if (d < 0 || (d & 1)) { bad = 3; return; }
            if (m == nm - 1 && nend < MAXEND) { endround[nend] = cur_round; endd[nend++] = d; }
            if ((d & 3) == 0) {                  /* swap: marker to g + d/2 - 1, gap to g + d/2 + 1 */
                if (d == 0 && !wall_free(g, gi)) { bad = 17; return; }
                T[gi] = 'M'; P[gi] = g + d / 2 - 1; T[m] = 'G'; P[m] = g + d / 2 + 1; gi = m;
            } else {                             /* merge: a wall at g + d/2 + 3, a packet from it */
                if (d == 2 && !wall_free(g, gi) && T[gi - 1] != 'M' && T[gi - 1] != 'B') { bad = 18; return; }
                del_at(gi); T[gi] = 'W'; P[gi] = g + d / 2 + 3; gi = packet_back(gi);
            }
        } else if (t == 'W') {                   /* the gap meets a wall: both go, a shift runs right */
            del_at(m); del_at(gi); gi = shift_from(gi);
        } else if (t == 'B') {                   /* a pass reaches a block: a wall one cell left, the gap sleeps */
            if (P[m] < g + 5) { bad = 19; return; }
            T[m] = 'W'; P[m] -= 1; gi = shift_from(m + 1);
        } else { bad = 4; return; }
        if (bad || halted) return;
    }
    if (bad || halted) return;
    ll extra = 2;                                /* the packet reached the left end: a new round two cells left */
    if (nm > 0 && T[0] == 'M' && P[0] == 0) { T[0] = 'W'; P[0] = 1; extra = 4; }
    for (int i = 0; i < nm; i++) P[i] += extra;
    W += extra; ins_at(0, 'G', 1);
}
