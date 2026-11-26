"""Worst-case test of the floor (README, "Ninth pass").  Token rules of py/tokz.py, exact integers.

usage: python3 py/adversary.py R0 R1 [STRATEGY ...]        strategies: O II rand (default: all three)

From round R0 to round R1, before every round's visit, an adversary rewrites every digit of the digit-only end Z
that lies at height 2m - 8 or more (everything above the exact layers; m = leading doublers of the round tape):

  O     all of them 000   (the defect crosses each in one step and arrives at the floor with all its visits)
  II    all of them 100, in pairs (crossed as well)
  rand  a fresh random mix of 000 and pairs 100 100

So the irregular and frozen digits never stop a defect that reaches Z, and the adversary repeats this every round.
Printed per strategy: the rounds whose defect died past the last doubler, its death height, the top of the exact
layers after that round and after the next even rounds (how fast the floor heals), and the largest need nx U
(the defect gets 2^m visits).
"""
import random
import sys
from fractions import Fraction as Fr

sys.setrecursionlimit(1000000)
import fuel
from conveyor import heights, visit, next_round, lead, exact_height, zstart


def rewrite(s, m, strategy):
    hs, z = heights(s), zstart(s)
    idx = [p for p in range(z, len(s)) if hs[p] >= 2 * m - 8]
    if strategy == 'O':
        for p in idx: s[p] = 'O'
    elif strategy == 'II':
        for p in idx: s[p] = 'I'
        if len(idx) % 2: s[idx[-1]] = 'O'
    elif strategy == 'rand':
        p = 0
        while p < len(idx):
            if random.random() < 0.5 or p + 1 >= len(idx):
                s[idx[p]] = 'O'; p += 1
            else:
                s[idx[p]] = s[idx[p + 1]] = 'I'; p += 2
    else:
        raise ValueError(strategy)


def run(strategy, R0, R1, seed=1):
    random.seed(seed)
    s = list('LLLzLLOLOI')                      # round 6, as in py/tokz.py
    rows = []
    for k in range(6, R1 + 1):
        m = lead(s)
        if k >= R0: rewrite(s, m, strategy)
        hs = heights(s)
        W, K = visit(s)
        if k >= R0:
            assert K is not None, 'round %d: the defect did not die' % k
            mm, nd = fuel.round_need(s)
            assert nd <= 2 ** mm, 'round %d: need %d exceeds 2^%d' % (k, nd, mm)
            e = None
            if k % 2 == 0: e = exact_height(W, heights(W), Fr(16, 15) - Fr(288, 127) / 2 ** m) - 2 * m
            rows.append((k, m, hs[K] - 2 * m, e, nd, K >= zstart(s)))
        s = next_round(W)
    return rows


def report(strategy, rows):
    print('strategy %s, rounds %d to %d' % (strategy, rows[0][0], rows[-1][0]))
    inz = [i for i, r in enumerate(rows) if r[5]]
    heal = 0
    for i in inz:
        k, m, dh, e, nd, _ = rows[i]
        tops, j = [], i
        while j < len(rows) and len(tops) < 4:
            if rows[j][3] is not None: tops.append(rows[j][3])
            j += 1
        back = next((rows[j][0] - k for j in range(i, len(rows)) if rows[j][3] is not None and rows[j][3] >= -12), None)
        if back is not None: heal = max(heal, back)
        print('  round %5d  m %4d  death at height 2m%+d  floor top - 2m in the next even rounds: %s' % (k, m, dh, tops))
    ev = [r[3] for r in rows[8:] if r[3] is not None]
    gaps = [rows[b][0] - rows[a][0] for a, b in zip(inz, inz[1:])]
    print('  defects dying past the last doubler: %d of %d rounds, smallest gap %s rounds; lowest death 2m%+d; '
          'lowest floor top 2m%+d; floor top back at 2m-12 or more within %d rounds; largest need %d' %
          (len(inz), len(rows), min(gaps) if gaps else '-', min(r[2] for r in rows), min(ev), heal,
           max(r[4] for r in rows)), flush=True)


if __name__ == '__main__':
    R0, R1 = int(sys.argv[1]), int(sys.argv[2])
    for st in sys.argv[3:] or ['O', 'II', 'rand']:
        report(st, run(st, R0, R1))
