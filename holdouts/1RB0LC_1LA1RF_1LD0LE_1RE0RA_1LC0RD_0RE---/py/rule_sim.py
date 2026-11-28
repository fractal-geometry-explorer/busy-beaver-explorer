"""The one-block lists of 1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---, predicted from the tripling rules.

`block_sim.py blocks` reaches its one-block moments by extrapolating any stretch that repeats (`Periodic`), which
is not a lemma.  This simulator does without it.  It runs the same stack of cells, runs of pairs and blocks of
movers, with only two kinds of skip:

  - the lemma-shaped skips of `block_sim.run_bounces`: a stretch of a transfer (two bounces run and checked, the
    rest by `walkm`'s arithmetic) and the drain of a lone block's first gap;
  - the rebuild's copy rule (README, "the rebuild's tripling, gap by gap"): at the start of a transfer
    `M[g ..] 0 n0 M[f ..]` in state S1 (n0 = 4), S0 (n0 = 3, the first gap shown one pair short) or S2 (n0 = 2),
    with fuel f, a gap g is copied when f > g' + 1 (g' the gap as shown): it is taken off the left block, the
    transducer's output h is put at the far end of the right block, and the fuel drops by g' + 2 when the next
    state is S1 and g' + 3 when it is S0.

        S1: g even -> 3g + 4, stay in S1;  g odd -> 3g + 8, to S0
        S0: g even -> 3g + 4, stay in S0;  g odd -> 3g,     to S1
        S2: g even -> 3g + 2, to S1;       g odd -> 3g + 6, to S0

    A run of a repeated gap or pair in the left block is copied a whole period at a time (one or two passes of
    the pattern, until the state comes back), as many periods as the fuel allows.  The last two gaps of a left
    block, and any copy that would leave less than 8 pairs of fuel beyond the next gap, are left to the bounces.

Everything else (drain ends, nesting, un-nesting, the reservoir's level changes, the one-block starts) is run
bounce by bounce.  The step count is not kept: the copy rule says what a copy leaves, not what it costs.

usage:  python3 py/rule_sim.py N     the one-block moments of the first N of them, printed as `block_sim.py blocks`
                                     prints them (lists longer than 400 characters cut to their two ends)
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import block_sim as b

N0 = {1: 4, 0: 3, 2: 2}
STATE = {4: 1, 3: 0, 2: 2}
MARGIN = 8


def tri(st, g):
    """the transducer: (output, next state)"""
    if st == 1: return (3 * g + 4, 1) if g % 2 == 0 else (3 * g + 8, 0)
    if st == 0: return (3 * g + 4, 0) if g % 2 == 0 else (3 * g, 1)
    return (3 * g + 2, 1) if g % 2 == 0 else (3 * g + 6, 0)


def drop(st_next, shown):
    return shown + (2 if st_next == 1 else 3)


def copy_skip(Y):
    """apply the copy rule at a transfer start; returns the number of gaps copied"""
    sh = b._transfer_shape(Y)
    if not (sh and sh[1] == '0' and sh[2] in STATE): return 0
    st = STATE[sh[2]]
    L, R = Y[-4][1], Y[-1][1]
    if not (isinstance(L, b.RQ) and isinstance(R, b.RQ)) or R.R[0][1] != 1 or len(R.R[0][0]) != 1: return 0
    f = R.pop_first()
    if st == 0: L.add_first(1)          # the true gap, as the transducer reads it
    copied = 0
    while L.size() > 2:
        pat, c = L.R[0]
        # one gap at a time while the front entry is a single gap or the state is S2
        if c == 1 or st == 2:
            g = pat[0]; shown = g - 1 if st == 0 else g
            h, s2 = tri(st, g); d = drop(s2, shown)
            nxt = L.R[1][0][0] if c == 1 else (pat[1] if len(pat) > 1 else pat[0])
            if f - d < nxt + MARGIN or f <= shown + 1: break
            L.pop_first(); R.append(h); f -= d; st = s2; copied += 1
            continue
        # a run: one period is one or two passes of the pattern, until the state comes back
        for reps in (1, 2, 3):
            s_ = st; outs = []; d = 0; ok = True
            for _ in range(reps):
                for g in pat:
                    shown = g - 1 if s_ == 0 else g
                    h, s2 = tri(s_, g); d += drop(s2, shown); outs.append(h); s_ = s2
            if s_ == st: break
        else:
            break
        per = reps                       # entries of the run used by one period
        # the copy condition is checked at the last period, where the fuel is lowest; the next gap after it
        # must still be copyable with MARGIN to spare
        mx = max(pat) + MARGIN + 2
        m = min((c - 1) // per, (f - mx) // d if f > mx else 0)
        if m <= 0:
            # a single gap of the run, if it fits
            g = pat[0]; shown = g - 1 if st == 0 else g
            h, s2 = tri(st, g); dd = drop(s2, shown)
            nxt = pat[1] if len(pat) > 1 else pat[0]
            if f - dd < nxt + MARGIN or f <= shown + 1: break
            L.pop_first(); R.append(h); f -= dd; st = s2; copied += 1
            continue
        L.R[0][1] -= m * per; L.S -= sum(pat) * m * per; L.n -= len(pat) * m * per
        R.push_entry(tuple(outs), m)
        f -= m * d; copied += m * per * len(pat)
    if st == 0: L.add_first(-1)
    R.prepend(f)
    Y[-2] = N0[st]
    return copied


def main():
    nmom = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    ms, Y, steps = b._exact_start()
    b.CFG['periodic'] = False
    t0 = time.time(); single = False; seen = 0; tp = t0
    while seen < nmom:
        b.run_bounces(Y, True); b.normalize(Y)
        if copy_skip(Y): b.normalize(Y)
        one = len(Y) == 3 and b.isM(Y[2])
        if one and not single:
            q = Y[2][1]; s_ = b._rle_runs(q.runs())
            print('one block, %d movers, hash %d: %s' % (q.size(), b.qhash(q), s_ if len(s_) < 400 else s_[:200] + ' ... ' + s_[-160:]),
                  '%.0fs' % (time.time() - t0), flush=True)
            seen += 1
        single = one
        if os.environ.get('PROGRESS') and time.time() - tp > float(os.environ['PROGRESS']):
            tp = time.time(); qs = [t[1] for t in Y if b.isM(t)]
            print('  %d items, %d movers' % (len(Y), sum(q.size() for q in qs)), flush=True)


if __name__ == '__main__':
    main()
