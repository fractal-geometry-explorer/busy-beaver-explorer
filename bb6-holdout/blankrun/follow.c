/* follow: the machine's run from blank tape in the mark model (fast.h), cycle by cycle (clean tape to clean tape),
   with every round start of three walls analysed as it comes.

   A pass start is a round start G 1, W a, W b, W c of width W with every gap >= 448 and the phase-0 parities
   (PassStart448 in ../lean/BB6/Ends.lean); R = W - c - 1, L = 147 b + 280 W - 392 c - 578, D = W - b.  From a pass
   start the stretch of the loop's chain runs to its end event (EndEvent): a landing (StepMap and StepWall: a full pass
   after 8 rounds, a half pass after 2, a break of the chain at round 7; three walls with the landing's parities), or a
   round start that is not three walls after the run has left phase 0 (after round 1 not B W, after round 2 not M B) or
   its end meetings have left the halving chain (ChainNext).  Each three-wall round start gets a code for how the run
   reached it:
     E  a pass start reached from outside the loop's chain (an entry)
     F, H, 7   a landing with every gap >= 448 (full pass, half pass, round-7 break): the chain goes on from it
     f, h, s   a landing with a gap below 448 (the chain ends there)
     i  a pass start inside the stretch of an earlier one that is neither a landing nor an end
     x  any other three-wall round start
   For each pass start: sigma = 3 log2(W/R) + 2 log2(|L|/W) (the lock: a close through the loop needs
   log2 W <= sigma + 6.38), the scale distance to the eight halting families of ../lean/thm/PassOpenHalt.lean
   (max(|log2(R/R0)|, |log2(D/D0)|), minimised over the families), the same for where each step from it would land,
   and Q = D + 2R + 22: on the main route of the halts past the chain's end the run meets the end at x = Q/4 - 2 off the
   chain, and the halting lanes have Q = 2^(j+2) (x = 2^j - 2, then halving to a close at 0), so the odd part u of Q
   (Q = 2^v u) measures how far the run is from a lane: log2 u = 0 on a lane (log2 3 on the 3 2^j - 2 route).  And the
   slack max(64R + 6 - W, 64D - 15W) / W in the condition W <= 64R + 6 or 15W <= 64D that a pass start above 2^41
   needs for a halt from blank tape (negative: the pass start fails both).

   Parallel stretches.  Paths of clean tapes merge: two paths that start a few hundred apart meet within a few dozen
   cycles, and from a shared clean tape on they are the same.  So a stretch started at any clean tape n = START
   (n = 2 mod 3, as every clean tape of the run is) joins the true run soon after, and stitch.py checks where: each
   stretch writes the clean tapes of the window [START, START + ZONE) at its head and of [END, END + ZONE) at its tail
   (V lines), and the true run (the previous stretch's tail) must meet a clean tape of the next stretch's head inside
   the window.  A stretch counts only the cycles that start at a clean tape n in [START + ZONE, END + ZONE) (from blank
   tape: [0, END + ZONE)), so the stretches' counts add up to the true run's exactly once the joins are checked.

   usage: follow blank END ZONE [ALL_BITS]          from blank tape (roundStart [] 5) to the first clean tape >= END + ZONE
          follow chunk START END ZONE [ALL_BITS]    from the clean tape START
          follow pass A B C W NR                    NR rounds from the round start G 1, W A, W B, W C of width W
   ALL_BITS (default 34): every three-wall round start of width below 2^ALL_BITS is written (T lines); above, those of a
   1/1024 sample of the cycles (by a hash of n, T lines) and the notable ones (N lines): every three-wall round start
   other than an entry or a half-pass landing, and every pass start that sets a record of the stretch (largest sigma,
   v2(Q)/log2 Q or chain position; smallest family distance, its next-step version, R, R/W, D/W, slack or log2 u), is
   in a family or has Q = 2^v or 3 2^v, or has R < 2048, D < 65536 or 15W > 64D.

   Output: V n cycle rounds (window clean tapes), K k W n cycle rounds (the clean tape first reaching width 2^k),
   P n cycle rounds (the first clean tape at or past each multiple of 10^11), C n cycle chain (a cycle whose end
   meetings make a halving chain of 11 or more; cycle = the cycles before n),
   T/N n r a b c W code chainpos sigma famdist famdist_next v2Q log2u flags (three-wall round starts: round r of the
   cycle from clean tape n), H n cycle halvings chain d W (closest end-meeting records), S ... (statistics per binary
   length of the width, at every 2^k from 2^30 and at the end), DONE.  Cycle and round counts are relative to the
   stretch's start; stitch.py makes them absolute. */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include "fast.h"
typedef __int128 i128;

static int ctz128(i128 x) { if (x == 0) return 127; if (x < 0) x = -x; int k = 0; while (!(x & 1)) { x >>= 1; k++; } return k; }
static int lg(ll x) { return x <= 0 ? -1 : 63 - __builtin_clzll((unsigned long long)x); }   /* floor(log2 x) */
static ll pred(ll d) { return (d % 4 == 2) ? (d - 2) / 2 : d / 2 + 4; }
static int chain_next(ll d, ll d2) { return (d % 4 == 0 && d2 == d / 2 + 4) || (d % 4 == 2 && d2 == (d - 2) / 2); }

/* ---- the eight families (W0, R0, b0, k): b = b0 + 2^k t, W = W0 + 2^k t, right part D = W - b = W0 - b0 ---- */
static const ll FW0[8] = {2368, 2376, 2460, 2656, 2760, 2872, 2962, 13400};
static const ll FR0[8] = {466, 402, 578, 178, 914, 474, 210, 186};
static const ll Fb0[8] = {1274, 956, 1304, 2010, 1084, 1794, 2288, 9698};
static const int Fk[8] = {15, 14, 14, 14, 15, 15, 13, 17};
static double famdist(double R, double D) {
    double best = 1e9;
    if (R <= 0 || D <= 0) return best;
    for (int f = 0; f < 8; f++) {
        double x = fabs(log2(R / (double)FR0[f])), y = fabs(log2(D / (double)(FW0[f] - Fb0[f])));
        double m = x > y ? x : y; if (m < best) best = m;
    }
    return best;
}
static int in_family(ll a, ll b, ll c, ll w) {
    ll R = w - c - 1, D = w - b;
    for (int f = 0; f < 8; f++)
        if (R == FR0[f] && D == FW0[f] - Fb0[f] && b >= Fb0[f] && ((b - Fb0[f]) & ((1LL << Fk[f]) - 1)) == 0 &&
            (a & 1) && a >= 448 && a + 448 <= b) return f + 1;
    return 0;
}

/* ---- statistics per binary length of the width (bin = floor(log2 W)) ---- */
#define NB 64
static const char CODES[] = "EFH7fhsix";
typedef struct {
    long long cycles, rounds, tw, ps, code[9], infam, sample_cycles, qpow2, q3pow2, wide1, wide2, wideany;
    long long hlr[NB], hld[NB], hv2R[NB], hv2L[NB], hv2Q[NB], hlu[NB], hchain[32], hhalv[NB];
    double maxsig, maxsigmargin, minR, minD, mindelta, mindelta_next, maxh, maxq, maxv2qr, minlu;
    double minRW, minDW, minslack, mRW[9], mDW[9];  /* exact minima of R/W, D/W and the wide slack; per code too */
    long long failboth[9];                           /* pass starts failing both wide conditions, per code */
    long long maxchain, maxv2Q;
} Bin;
static Bin S[NB];
static long long endchain_hist[64];
static long long ncyc, nround;              /* relative counters */
static long long nquick, nqcheck; static int NOSKIP;
static int ALLBITS = 34;
static ll own_lo, own_hi;                   /* the cycles counted: start n in [own_lo, own_hi) */
static ll win1_lo, win1_hi, win2_lo, win2_hi;
#define PSTEP 100000000000LL                /* P lines: the first clean tape at or past each multiple of 10^11 */

static void bin_init(void) {
    for (int b = 0; b < NB; b++) {
        S[b].maxsig = -1e9; S[b].maxsigmargin = -1e9; S[b].minR = 1e30; S[b].minD = 1e30; S[b].mindelta = 1e9;
        S[b].mindelta_next = 1e9; S[b].maxh = -1; S[b].maxv2qr = -1; S[b].minlu = 1e9;
        S[b].minRW = S[b].minDW = S[b].minslack = 1e9;
        for (int c = 0; c < 9; c++) S[b].mRW[c] = S[b].mDW[c] = 1e9;
    }
}
static void hist(const char *name, const long long *h, int n) {
    printf(" %s", name); for (int i = 0; i < n; i++) if (h[i]) printf(" %d:%lld", i, h[i]);
}
static void dump_stats(const char *tag) {
    for (int b = 0; b < NB; b++) {
        Bin *s = &S[b]; if (!s->cycles && !s->tw) continue;
        printf("S %s %d cycles %lld rounds %lld tw %lld ps %lld", tag, b, s->cycles, s->rounds, s->tw, s->ps);
        for (int c = 0; c < 9; c++) printf(" %c %lld", CODES[c], s->code[c]);
        printf(" infam %lld samplecycles %lld qpow2 %lld q3pow2 %lld wide1 %lld wide2 %lld wideany %lld",
               s->infam, s->sample_cycles, s->qpow2, s->q3pow2, s->wide1, s->wide2, s->wideany);
        printf(" maxsig %.4f maxsigmargin %.4f minR %.0f minD %.0f mindelta %.4f mindelta_next %.4f maxchain %lld maxh %.4f"
               " maxv2Q %lld maxv2qr %.4f minlu %.4f",
               s->maxsig, s->maxsigmargin, s->minR, s->minD, s->mindelta, s->mindelta_next, s->maxchain, s->maxh,
               s->maxv2Q, s->maxv2qr, s->minlu);
        if (s->ps) printf(" minRW %.8f minDW %.8f minslack %.8f", s->minRW, s->minDW, s->minslack);
        for (int c = 0; c < 9; c++)
            if (s->mRW[c] < 1e8) printf(" mRW_%c %.8f mDW_%c %.8f", CODES[c], s->mRW[c], CODES[c], s->mDW[c]);
        for (int c = 0; c < 9; c++) if (s->failboth[c]) printf(" fb_%c %lld", CODES[c], s->failboth[c]);
        hist("lr", s->hlr, NB); hist("ld", s->hld, NB); hist("v2R", s->hv2R, NB); hist("v2L", s->hv2L, NB);
        hist("v2Q", s->hv2Q, NB); hist("lu", s->hlu, NB); hist("chain", s->hchain, 32); hist("halv", s->hhalv, NB);
        printf("\n");
    }
    printf("S %s endchain", tag); for (int i = 0; i < 64; i++) if (endchain_hist[i]) printf(" %d:%lld", i, endchain_hist[i]);
    printf(" tw_canon %lld cycles %lld rounds %lld\n", tw_canon, ncyc, nround);
    fflush(stdout);
}

/* ---- the current cycle: three-wall round starts, and the mark types of every round start ---- */
typedef struct { ll a, b, c, w; int r; i128 L; int ps; } TW;
#define MAXT 512
static TW tws[MAXT]; static int nt;
#define MAXR (1 << 20)
static unsigned short rsig[MAXR + 2];       /* round start r: number of marks after the gap << 8 | their types */
static inline unsigned short sig_now(void) {
    if (nm - 1 > 4) return 0xFFFF;
    unsigned short s = (unsigned short)((nm - 1) << 8);
    for (int i = 1; i < nm; i++) s |= (unsigned short)(MT(i) << (2 * (i - 1)));
    return s;
}
#define SIG2(t1, t2) ((unsigned short)((2 << 8) | (t1) | ((t2) << 2)))

/* is t a landing of the loop's chain from the pass start s (StepMap, StepWall and the landing's parities)?
   0 = no, 1 full, 2 half, 3 break7 */
static int landing_kind(const TW *s, const TW *t) {
    int n = t->r - s->r; ll E = s->w, R = s->w - s->c - 1; i128 L = s->L;
    ll Wt = t->w, Rt = t->w - t->c - 1; i128 Lt = t->L;
    if (!((t->a & 1) && !(t->b & 1) && (Wt % 4) == 0 && !(Rt & 1) && Rt >= 2)) return 0;
    if (n == 8 && 16 * Rt == R && 64 * Lt == L && Wt == E + 24 &&
        (i128)9408 * t->a == L + (i128)2464 * E - (i128)980 * R + 99264) return 1;
    if (n == 2 && 2 * Rt == R && 2 * Lt == L + (i128)35 * E - (i128)147 * R - 60 && Wt == E + 6 && E % 4 == 2 &&
        (i128)294 * t->a == L + (i128)112 * E - (i128)392 * R + 1656) return 2;
    if (n == 7 && (i128)4704 * Rt == (i128)476 * E + (i128)980 * R - L + 15984 &&
        (i128)96 * Lt == L + (i128)1120 * E + (i128)1666 * R + 50328 && Wt == E + 24 &&
        (i128)2352 * t->a == L + (i128)406 * E - (i128)539 * R + 19884) return 3;
    return 0;
}
/* the families' scale distance of where each step from (E, R, L) would land (real numbers: R' and D' = W' - b') */
static double next_delta(ll E, ll R, i128 L) {
    double best = 1e9, Ld = (double)L, Ed = (double)E, Rd = (double)R, d;
    { double Wp = Ed + 24, Rp = Rd / 16, Lp = Ld / 64, bp = (Lp + 112 * Wp - 392 * Rp + 186) / 147;
      d = famdist(Rp, Wp - bp); if (d < best) best = d; }
    if (E % 4 == 2) { double Wp = Ed + 6, Rp = Rd / 2, Lp = (Ld + 35 * Ed - 147 * Rd - 60) / 2, bp = (Lp + 112 * Wp - 392 * Rp + 186) / 147;
      d = famdist(Rp, Wp - bp); if (d < best) best = d; }
    { double Wp = Ed + 24, Rp = (476 * Ed + 980 * Rd - Ld + 15984) / 4704, Lp = (Ld + 1120 * Ed + 1666 * Rd + 50328) / 96,
      bp = (Lp + 112 * Wp - 392 * Rp + 186) / 147; d = famdist(Rp, Wp - bp); if (d < best) best = d; }
    return best;
}

static double rec_sig = -1e9, rec_delta = 1e9, rec_dnext = 1e9, rec_v2qr = -1, rec_lu = 1e9, rec_q = 0;
static double rec_RW = 1e9, rec_DW = 1e9, rec_slack = 1e9;
static long long rec_chain = 0; static ll rec_minR = -1;

/* one three-wall round start, with its code (index into CODES) and chain position */
static void record(ll n, const TW *t, int code, int chainpos, int sampled) {
    ll R = t->w - t->c - 1, D = t->w - t->b; int b = lg(t->w);
    Bin *s = &S[b]; s->tw++; s->code[code]++;
    double sig = -1e9, delta = 1e9, dnext = 1e9, lu = -1, RW = 1e9, DW = 1e9, slack = 1e9; int v2Q = -1, fam = 0, qp = 0;
    if (t->ps) {
        s->ps++;
        s->hlr[lg(t->w) - lg(R) < 0 ? 0 : lg(t->w) - lg(R)]++;
        s->hld[lg(t->w) - lg(D) < 0 ? 0 : lg(t->w) - lg(D)]++;
        int v2R = ctz128((i128)R), v2L = ctz128(t->L); s->hv2R[v2R > 63 ? 63 : v2R]++; s->hv2L[v2L > 63 ? 63 : v2L]++;
        if ((double)R < s->minR) s->minR = (double)R;
        if ((double)D < s->minD) s->minD = (double)D;
        double aL = (double)(t->L < 0 ? -t->L : t->L);
        sig = 3 * log2((double)t->w / (double)R) + 2 * log2(aL / (double)t->w);
        if (sig > s->maxsig) s->maxsig = sig;
        double margin = sig + 6.38 - log2((double)t->w); if (margin > s->maxsigmargin) s->maxsigmargin = margin;
        delta = famdist((double)R, (double)D); if (delta < s->mindelta) s->mindelta = delta;
        dnext = next_delta(t->w, R, t->L); if (dnext < s->mindelta_next) s->mindelta_next = dnext;
        fam = in_family(t->a, t->b, t->c, t->w); if (fam) s->infam++;
        if (chainpos > s->maxchain) s->maxchain = chainpos;
        ll Q = D + 2 * R + 22; v2Q = ctz128((i128)Q); ll u = Q >> v2Q;
        s->hv2Q[v2Q > 63 ? 63 : v2Q]++; if (v2Q > s->maxv2Q) s->maxv2Q = v2Q;
        double v2qr = (double)v2Q / log2((double)Q); if (v2qr > s->maxv2qr) s->maxv2qr = v2qr;
        lu = log2((double)u); if (lu < s->minlu) s->minlu = lu;
        { int lu2 = lg(u); s->hlu[lu2 < 0 ? 0 : lu2 > 63 ? 63 : lu2]++; }
        if (u == 1) { s->qpow2++; qp = 1; } else if (u == 3) { s->q3pow2++; qp = 3; }
        /* the necessary condition of the "Find when the chain lands on a halt" thread for a halt above 2^41 */
        int w1 = t->w <= 64 * R + 6, w2 = 15 * (i128)t->w <= 64 * (i128)D;
        s->wide1 += w1; s->wide2 += w2; s->wideany += (w1 || w2);
        /* how close it comes to failing both: slack = max(64R + 6 - W, 64D - 15W) / W (negative: fails both) */
        ll s1 = 64 * R + 6 - t->w, s2 = 64 * D - 15 * t->w;
        RW = (double)R / (double)t->w; DW = (double)D / (double)t->w; slack = (double)(s1 > s2 ? s1 : s2) / (double)t->w;
        if (RW < s->minRW) s->minRW = RW;
        if (DW < s->minDW) s->minDW = DW;
        if (slack < s->minslack) s->minslack = slack;
        if (RW < s->mRW[code]) s->mRW[code] = RW;
        if (!w1 && !w2) s->failboth[code]++;
        if (DW < s->mDW[code]) s->mDW[code] = DW;
    }
    int notable = 0;
    if (t->ps) {
        if (sig > rec_sig) { rec_sig = sig; notable = 1; }
        if (delta < rec_delta) { rec_delta = delta; notable = 1; }
        if (dnext < rec_dnext) { rec_dnext = dnext; notable = 1; }
        if (chainpos > rec_chain) { rec_chain = chainpos; notable = 1; }
        if (rec_minR < 0 || R < rec_minR) { rec_minR = R; notable = 1; }
        double v2qr = (double)v2Q / log2((double)(D + 2 * R + 22));
        if (v2qr > rec_v2qr) { rec_v2qr = v2qr; notable = 1; }
        if (lu < rec_lu) { rec_lu = lu; notable = 1; }
        if (RW < rec_RW) { rec_RW = RW; notable = 1; }
        if (DW < rec_DW) { rec_DW = DW; notable = 1; }
        if (slack < rec_slack) { rec_slack = slack; notable = 1; }
        if (fam || qp || R < 2048 || D < 65536 || 15 * (i128)t->w > 64 * (i128)D) notable = 1;
    }
    /* every landing other than a half pass, and every i and x, is rare enough to write */
    if (code != 0 && code != 2) notable = 1;
    if (b < ALLBITS || sampled || notable)
        printf("%c %lld %d %lld %lld %lld %lld %c %d %.4f %.4f %.4f %d %.4f%s%s\n", (b < ALLBITS || sampled) ? 'T' : 'N',
               (long long)n, t->r, (long long)t->a, (long long)t->b, (long long)t->c, (long long)t->w, CODES[code], chainpos,
               t->ps ? sig : 0.0, t->ps ? delta : 0.0, t->ps ? dnext : 0.0, v2Q, t->ps ? lu : 0.0,
               fam ? " FAMILY" : "", qp == 1 ? " QPOW2" : qp == 3 ? " Q3POW2" : "");
}

/* analyse the cycle's three-wall round starts in order, following each pass start's stretch to its end event */
static void analyse(ll n, int sampled) {
    int head = -1, chainpos = 0, ei = 0, broken = 0, have = 0, entry_bin = 0; ll lastd = 0;
    int ti = 0, last = tws[nt - 1].r;
    for (int r = tws[0].r; r <= last; r++) {
        /* the end meetings of round r belong to the stretch of the head (round start r_h < r) */
        while (ei < nend && endround[ei] <= r) {
            if (head >= 0 && endround[ei] > tws[head].r) {
                ll d = endd[ei]; if (have && !chain_next(lastd, d)) broken = 1; lastd = d; have = 1;
            }
            ei++;
        }
        int isT = ti < nt && tws[ti].r == r;
        if (head >= 0 && r > tws[head].r) {
            if (isT) {
                int k = landing_kind(&tws[head], &tws[ti]);
                if (k) {
                    TW *t = &tws[ti];
                    if (t->ps) { chainpos++; record(n, t, k, chainpos, sampled); head = ti; broken = 0; have = 0; }
                    else { record(n, t, 3 + k, chainpos + 1, sampled); S[entry_bin].hchain[chainpos + 1 > 31 ? 31 : chainpos + 1]++; head = -1; }
                    ti++; continue;
                }
                /* a three-wall round start inside the stretch: no end event */
                record(n, &tws[ti], tws[ti].ps ? 7 : 8, chainpos, sampled); ti++; continue;
            } else {
                int dr = r - tws[head].r;
                int left = (dr == 1 && rsig[r] != SIG2(tB, tW)) || (dr == 2 && rsig[r] != SIG2(tM, tB));
                if (left || broken) { S[entry_bin].hchain[chainpos > 31 ? 31 : chainpos]++; head = -1; }
            }
        }
        if (isT) {
            TW *t = &tws[ti];
            if (t->ps) { record(n, t, 0, 0, sampled); head = ti; chainpos = 0; broken = 0; have = 0; entry_bin = lg(t->w); }
            else record(n, t, 8, 0, sampled);
            ti++;
        }
    }
    if (head >= 0) S[entry_bin].hchain[chainpos > 31 ? 31 : chainpos]++;   /* the stretch outlasts the last three walls */
}

static void note_tw(int r) {
    if (nm == 4 && MT(1) == tW && MT(2) == tW && MT(3) == tW && nt < MAXT) {
        TW *t = &tws[nt++]; t->a = realP(1); t->b = realP(2); t->c = realP(3); t->w = realW(); t->r = r;
        t->L = (i128)147 * t->b + (i128)280 * t->w - (i128)392 * t->c - 578;
        ll R = t->w - t->c - 1;
        t->ps = (t->a & 1) && !(t->b & 1) && !(t->w & 1) && !(R & 1) && R >= 2 && t->a >= 448 && t->a + 448 <= t->b &&
                t->b + 448 + R + 1 <= t->w;
    }
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: follow blank END ZONE [ALL_BITS] | chunk START END ZONE [ALL_BITS] | pass A B C W NR\n"); return 2; }
    bin_init();
    if (argv[1][0] == 'p') {
        ll a = atoll(argv[2]), b = atoll(argv[3]), c = atoll(argv[4]), w = atoll(argv[5]); int nr = atoi(argv[6]);
        set_start(w); add_mark(tG, 1); add_mark(tW, a); add_mark(tW, b); add_mark(tW, c);
        nt = 0; nend = 0; ALLBITS = 64; note_tw(0); rsig[0] = sig_now();
        int r;
        for (r = 1; r <= nr && r <= MAXR; r++) {
            cur_round = r; do_round();
            if (halted || bad) { printf("round %d: %s %d\n", r, halted ? "halt" : "uncovered", bad); break; }
            rsig[r] = sig_now(); note_tw(r);
            printf("round %d: W %lld", r, (long long)realW()); for (int i = 1; i < nm; i++) printf(" %c %lld", "GMWB"[MT(i)], (long long)realP(i));
            printf("   end meetings:"); for (int i = 0; i < nend; i++) if (endround[i] == r) printf(" %lld", (long long)endd[i]); printf("\n");
        }
        if (nt) analyse(0, 1);
        return 0;
    }
    NOSKIP = getenv("NOSKIP") != NULL;
    int chunk = argv[1][0] == 'c';
    ll start = 0, end, zone;
    if (chunk) { start = atoll(argv[2]); end = atoll(argv[3]); zone = atoll(argv[4]); if (argc > 5) ALLBITS = atoi(argv[5]); }
    else { end = atoll(argv[2]); zone = atoll(argv[3]); if (argc > 4) ALLBITS = atoi(argv[4]); }
    if (chunk) {
        if (start % 3 != 2) { fprintf(stderr, "START must be 2 mod 3\n"); return 2; }
        set_start(2 * start + 6); add_mark(tG, 1); add_mark(tM, 2 * start + 4);
        own_lo = start + zone; win1_lo = start; win1_hi = start + zone;
    } else { set_start(5); add_mark(tG, 1); own_lo = -10; win1_lo = win1_hi = -10; }
    own_hi = end + zone; win2_lo = end; win2_hi = end + zone;
    printf("# follow %s start %lld end %lld zone %lld allbits %d\n", chunk ? "chunk" : "blank", (long long)start, (long long)end,
           (long long)zone, ALLBITS);
    int k_next = 0; while (k_next < 63 && ((ll)1 << k_next) <= realW()) k_next++;
    ll p_next = (start / PSTEP + 1) * PSTEP;
    for (;;) {
        ll w = realW(); ll n = (w - 6) / 2;
        int owned = n >= own_lo && n < own_hi;
        if ((n >= win1_lo && n < win1_hi) || (n >= win2_lo && n < win2_hi)) printf("V %lld %lld %lld\n", (long long)n, ncyc, nround);
        if (n >= own_hi) break;
        /* the quick classes (settled at 5 digits, every member n >= 32 follows them; used from 2^20 on): odd n -> n + 3
           in 2 rounds, n = 0 mod 4 -> n + 6 in 3, n = 6 mod 16 -> n + 9 in 5, n = 10 mod 16 -> n + 9 in 5 (halving
           chain 2), n = 2 mod 32 -> n + 12 in 6 (chain 2); none has a three-wall round start or an end meeting more
           than 1.42 halvings below the width.  Every 65,536th one is simulated and compared. */
        int qc = -1;
        if (n >= (1LL << 20) && !NOSKIP) qc = (n & 1) ? 0 : (n % 4 == 0) ? 1 : (n % 16 == 6) ? 2 : (n % 16 == 10) ? 3 : (n % 32 == 2) ? 4 : -1;
        if (qc >= 0 && ((++nquick) & 0xFFFF) != 0) {
            static const int QJ[5] = {3, 6, 9, 9, 12}, QR[5] = {2, 3, 5, 5, 6}, QC[5] = {1, 1, 1, 2, 2}, QB[5] = {0, 0, 0, 1, 1};
            ncyc++; nround += QR[qc];
            ll w2 = 2 * (n + QJ[qc]) + 6; set_start(w2); add_mark(tG, 1); add_mark(tM, w2 - 2);
            if (owned) {
                Bin *s = &S[lg(w)]; s->cycles++; s->rounds += QR[qc]; endchain_hist[QC[qc]]++; s->hhalv[QB[qc]]++;
                while ((w2 - 6) / 2 >= p_next) { printf("P %lld %lld %lld\n", (long long)((w2 - 6) / 2), ncyc, nround); p_next += PSTEP; }
                if ((((unsigned long long)n * 0x9E3779B97F4A7C15ULL) >> 54) == 0) s->sample_cycles++;
                while (k_next < 63 && w2 >= ((ll)1 << k_next)) {
                    printf("K %d %lld %lld %lld %lld\n", k_next, (long long)w2, (long long)((w2 - 6) / 2), ncyc, nround);
                    k_next++;
                    if (k_next > 30) dump_stats("partial");
                    fprintf(stderr, "n %lld cycles %lld rounds %lld\n", (long long)n, ncyc, nround);
                }
            } else { while (k_next < 63 && w2 >= ((ll)1 << k_next)) k_next++; while ((w2 - 6) / 2 >= p_next) p_next += PSTEP; }
            continue;
        }
        nend = 0; nt = 0; int r = 0; double qmax = 0; ll dmin = -1, wdmin = 0;
        for (;;) {
            cur_round = ++r; int ne0 = nend; ll w0 = realW();
            do_round(); nround++;
            if (halted || bad) {
                printf("STOP n %lld round %d: %s %d\n", (long long)n, r, halted ? "halt" : "uncovered", bad); fflush(stdout);
                fprintf(stderr, "STOP at n %lld round %d: halted %d bad %d\n", (long long)n, r, halted, bad); return 1;
            }
            for (int i = ne0; i < nend; i++) {      /* closest end meeting, as the ratio width / distance */
                ll d = endd[i]; double q = d > 0 ? (double)w0 / (double)d : 1e30;
                if (dmin < 0 || q > qmax) { qmax = q; dmin = d; wdmin = w0; }
            }
            if (r <= MAXR) rsig[r] = sig_now();
            if (nm == 4) note_tw(r);
            if (nm == 2 && MT(1) == tM && realP(1) == realW() - 2) break;
            if (r > MAXR) { printf("STOP n %lld: no clean tape in %d rounds\n", (long long)n, MAXR); return 1; }
        }
        if (qc >= 0) {                      /* the check of a quick class */
            static const int QJ[5] = {3, 6, 9, 9, 12}, QR[5] = {2, 3, 5, 5, 6}, QC[5] = {1, 1, 1, 2, 2}, QB[5] = {0, 0, 0, 1, 1};
            int best = nend > 0 ? 1 : 0, cur = 1;
            for (int i = 1; i < nend; i++) { if (endd[i] == pred(endd[i - 1])) { cur++; if (cur > best) best = cur; } else cur = 1; }
            if ((realW() - 6) / 2 != n + QJ[qc] || r != QR[qc] || best != QC[qc] || ilogb(qmax) != QB[qc] || nt != 0) {
                printf("STOP quick class %d check failed at n %lld\n", qc, (long long)n); return 1;
            }
            nqcheck++;
        }
        ncyc++;
        ll w2 = realW();
        if (owned) {
            int b = lg(w); Bin *s = &S[b]; s->cycles++; s->rounds += r;
            int best = nend > 0 ? 1 : 0, cur = 1;
            for (int i = 1; i < nend; i++) { if (endd[i] == pred(endd[i - 1])) { cur++; if (cur > best) best = cur; } else cur = 1; }
            endchain_hist[best < 63 ? best : 63]++;
            if (best >= 11) printf("C %lld %lld %d\n", (long long)n, ncyc - 1, best);
            while ((w2 - 6) / 2 >= p_next) { printf("P %lld %lld %lld\n", (long long)((w2 - 6) / 2), ncyc, nround); p_next += PSTEP; }
            double hrec = -1;
            if (dmin >= 0) {
                int hb = ilogb(qmax); s->hhalv[hb < 0 ? 0 : hb > 63 ? 63 : hb]++;
                if (qmax > s->maxq) { s->maxq = qmax; s->maxh = log2(qmax); }
                if (qmax > rec_q) hrec = log2(qmax);
            }
            int sampled = (((unsigned long long)n * 0x9E3779B97F4A7C15ULL) >> 54) == 0;
            if (sampled) s->sample_cycles++;
            if (nt > 0) analyse(n, sampled);
            if (hrec >= 2 && w > 1000) { rec_q = qmax; printf("H %lld %lld %.4f %d %lld %lld\n", (long long)n, ncyc, hrec, best, (long long)dmin, (long long)wdmin); }
            while (k_next < 63 && w2 >= ((ll)1 << k_next)) {
                printf("K %d %lld %lld %lld %lld\n", k_next, (long long)w2, (long long)((w2 - 6) / 2), ncyc, nround);
                k_next++;
                if (k_next > 30) dump_stats("partial");
                fprintf(stderr, "n %lld cycles %lld rounds %lld\n", (long long)n, ncyc, nround);
            }
        } else {
            while (k_next < 63 && w2 >= ((ll)1 << k_next)) k_next++;
            while ((w2 - 6) / 2 >= p_next) p_next += PSTEP;
        }
    }
    dump_stats("final");
    printf("DONE cycles %lld rounds %lld quick %lld checked %lld\n", ncyc, nround, nquick, nqcheck);
    return 0;
}
