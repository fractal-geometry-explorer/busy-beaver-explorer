"""The far end of the tape as a conveyor (README, "Eighth pass").  Token rules of py/tokz.py, exact integers.

usage: python3 py/conveyor.py ROUNDS [PERTURB_ROUND=200]

W_k is the clean tape the visit of round k leaves (before the next x is put in front), m the number of leading
doublers of round k's tape, h the doubler height of a word (doublers minus digits before it, counted from the
front).  v(W) = sum of 2^-h over the digits I.  Checked, for every round from 40 to ROUNDS:

 1. the value law   v(W_k) = 16/15 - c 2^-m + r,  c = 288/127 (k even), 145/127 (k odd), |r| < 2^-(2m-12)
    (so each round moves v by exactly 2/127 2^-m or 143/127 2^-m, up to the same error);
 2. for even k, the digit-only end Z of W_k is, digit for digit, the binary expansion of 16/15 - (288/127) 2^-m
    at every height below 2m - 8 (the "period 4" and "period 28" layers of the fifth pass);
 3. the defect's path never goes below height m - 1, and it dies at height at least 2m - 9;
 4. a defect that enters the end of the tape at any height between 5 and 2m - 8, as x, 1 or z, dies within 19
    words (so it can never cross the exact layers).

Then a perturbation test: flip one digit of Z at a height h < m in round PERTURB_ROUND and follow both runs.  The
flipped digit stays a single difference and moves exactly 4 heights up per round (v changes 16 times less each
round) until it reaches height m; it never moves down.
"""
import sys
from fractions import Fraction as Fr

sys.setrecursionlimit(1000000)
import tokz
from tokz import T


def heights(s):
    b, hs = 0, []
    for t in s:
        hs.append(b)
        b += 1 if t == 'L' else (-1 if t in 'OI' else 0)
    return hs


def visit(s):
    """The round's visit of A on the round tape s: (W, index where the defect died or None)."""
    T[:] = s
    tokz.stats['die'] = []
    tokz.An(1, 0)
    d = tokz.stats['die']
    return list(T), (d[-1][2] if d else None)


def next_round(W):
    s = list(W)
    s.insert(0, 'x')
    T[:] = s
    tokz.norm()
    while T and T[-1] == 'O': T.pop()
    return list(T)


def lead(s):
    m = 0
    while s[m] == 'L': m += 1
    return m


def value(W, hs):
    """v(W) as an exact fraction (heights may be negative near the far end)."""
    lo = min(hs[i] for i, t in enumerate(W) if t == 'I')
    top = max(hs) + 1
    n = 0
    for i, t in enumerate(W):
        if t == 'I': n += 1 << (top - hs[i])
    return Fr(n, 1 << (top - lo)) * Fr(2) ** lo if lo < 0 else Fr(n, 1 << top)


def zstart(W):
    j = len(W)
    while j > 0 and W[j - 1] != 'L': j -= 1
    return j


def exact_height(W, hs, target):
    """Largest H such that the digits of Z below height H agree with the binary expansion of target."""
    z = zstart(W)
    zd = sorted((hs[i], W[i]) for i in range(z, len(W)))
    lo, top = zd[0][0], zd[-1][0] + 1
    # integers in units of 2^-top, shifted so that the lowest height is allowed to be negative
    sh = top - min(lo, 0)
    tgt = target * 2 ** sh
    acc = 0
    for h, t in zd:
        if t == 'I': acc += 1 << (sh - h)
        if abs(acc - tgt) >= (1 << (sh - h)): return h
    return top

def band_window(W, hs, m):
    """Most words a defect eats when it enters Z at a height in [5, 2m-8], as x, 1 or z, with ample visits."""
    z, worst = zstart(W), 0
    for i in range(z, len(W)):
        if 5 <= hs[i] <= 2 * m - 8:
            for d in 'x1z':
                T[:] = ['L'] * 40 + [d] + W[i:i + 200]
                tokz.stats['die'] = []
                tokz.An(1, 0)
                dd = tokz.stats['die']
                if not dd or dd[-1][2] - 41 > 150: return None
                worst = max(worst, dd[-1][2] - 41)
    return worst


def main(R, PK):
    s = list('LLLzLLOLOI')                      # round 6, as in py/tokz.py
    worst = {'r': None, 'exact': None, 'path': None, 'death': None, 'late': None, 'band': 0}
    saved = None
    for k in range(6, R + 1):
        m = lead(s)
        hs = heights(s)
        W, K = visit(s)
        if k == PK: saved = list(s)
        if k >= 40:
            hw = heights(W)
            c = Fr(288, 127) if k % 2 == 0 else Fr(145, 127)
            r = (value(W, hw) - Fr(16, 15) + c / 2 ** m) * 2 ** (2 * m)
            worst['r'] = max(worst['r'] or 0, abs(r))
            assert abs(r) < 2 ** 12, (k, float(r))
            p = min(hs[m + 1:K + 1]) - m
            worst['path'] = p if worst['path'] is None else min(worst['path'], p)
            dh = hs[K] - 2 * m
            worst['death'] = dh if worst['death'] is None else min(worst['death'], dh)
            if k >= 500: worst['late'] = dh if worst['late'] is None else min(worst['late'], dh)
            if k % 2 == 0:
                e = exact_height(W, hw, Fr(16, 15) - Fr(288, 127) / 2 ** m) - 2 * m
                worst['exact'] = e if worst['exact'] is None else min(worst['exact'], e)
            if k % 50 == 0 or k == R:
                b = band_window(W, hw, m)
                worst['band'] = None if b is None or worst['band'] is None else max(worst['band'], b)
                print('round %6d  m %5d  r*2^(2m) %10.3f  exact Z below 2m%+d  path min h - m %d  death h - 2m %d  '
                      'band window %s' % (k, m, float(r), e if k % 2 == 0 else 0, p, dh, b), flush=True)
        s = next_round(W)
    print('rounds 40..%d: |r| 2^(2m) at most %.3f; Z exact below height 2m%+d (even rounds); path min height m%+d; '
          'death height at least 2m%+d (from round 500: 2m%+d); band window at most %s words' %
          (R, float(worst['r']), worst['exact'], worst['path'], worst['death'], worst['late'] or 0, worst['band']))
    if saved is None: return
    # perturbation test
    a = saved
    hs = heights(a)
    m0 = lead(a)
    for h in (5, m0 // 2, m0 - 12):
        idx = max(i for i in range(len(a)) if hs[i] == h and a[i] in 'OI')
        b = list(a)
        b[idx] = 'O' if a[idx] == 'I' else 'I'
        x, y, seen = a, b, []
        for r in range(m0):
            Wx, _ = visit(x)
            Wy, _ = visit(y)
            hx = heights(Wx)
            n = min(len(Wx), len(Wy))
            diffs = [t for t in range(1, n + 1) if Wx[-t] != Wy[-t]]
            mm = lead(x)
            if hx[-diffs[0]] >= mm - 6: break
            seen.append((len(diffs), hx[-diffs[0]]))
            x, y = next_round(Wx), next_round(Wy)
        steps = [seen[i + 1][1] - seen[i][1] for i in range(len(seen) - 1)]
        print('flip at height %d in round %d: %d rounds as a single difference (%s), heights %d -> %d, steps %s' %
              (h, PK, len(seen), all(d == 1 for d, _ in seen), seen[0][1], seen[-1][1], sorted(set(steps))))


if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]) if len(sys.argv) > 2 else 200)
