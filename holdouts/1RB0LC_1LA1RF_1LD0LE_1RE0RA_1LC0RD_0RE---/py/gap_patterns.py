"""Which gaps the moving movers have, and what reaches the right end.

    python3 holdouts/<M>/py/gap_patterns.py [MAXSTEPS] [EVERY]     (default 1e13, every 50th bounce; ~10 min)

Runs the exact simulator (`mover_sim.py`) and, every EVERY bounces, reads the gaps of the movers the head crosses
(`gs`, the rightmost first) after the first one, written as a pattern of `L` (three pairs or more), `2` and `1`, with
repeats merged.  It also prints, at every bounce where the rightmost gap is under two pairs (the next collision is at
the right end), the first eight gaps with 8 or more written as K.
"""
import collections
import itertools
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mover_sim as ms  # noqa: E402


def pattern(gs):
    out = []
    for j, (g, c) in enumerate(gs.r):
        if j == 0:
            c -= 1
            if c == 0:
                continue
        t = '1' if g == 1 else ('2' if g == 2 else 'L')
        if not out or out[-1] != t:
            out.append(t)
    return ''.join(out)


if __name__ == '__main__':
    stop = float(sys.argv[1]) if len(sys.argv) > 1 else 1e13
    every = int(sys.argv[2]) if len(sys.argv) > 2 else 50
    S = ms.start(); n = 0
    pats = collections.Counter(); ends = collections.Counter(); first = {}
    while S.steps < stop:
        n += 1
        if S.gs and n % every == 0:
            pats[pattern(S.gs)] += 1
        if S.gs and S.gs.first() < 2 and len(S.Z) == 1:
            k = ' '.join(str(g) if g < 8 else 'K' for g in itertools.islice(S.gs.gaps(), 8))
            ends[k] += 1; first.setdefault(k, S.steps)
        S.bounce()
    print('gap patterns after the first gap, sampled every %d bounces to step %d:' % (every, S.steps))
    for k, v in pats.most_common():
        print('  %-8s %d' % (k, v))
    print('first eight gaps when the rightmost is under two pairs:')
    for k, v in sorted(ends.items(), key=lambda x: first[x[0]]):
        print('  %-24s %6d times, first at step %d' % (k, v, first[k]))
