"""Crossings of 1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF as one map (see README, "Crossings as one map").

A crossing starts at a right turn `Turn w p s R` (lean/Wall.lean) where `nxt w p s` is `none`: the right sweep has used
up the whole frozen word. The tape is then the swept zone `W` (2-cell letters, nearest first) with prefix `p`,
and the head is in F or E (= W[0]) on `R`, which is blank or a single 1 (`r`). So everything until the next turn
with no lone 1 inside the zone depends on (W, p, r) alone. `crossing` runs the machine through it.

  python3 crossing.py run [N]   compare `crossing` with the real run for N steps (default 2*10^7), list the starts
  python3 crossing.py table     crossings from small words whose a-runs between b's are odd
"""
import sys
import itertools
from collections import Counter
from turnshape import T, tok_left, tok_right, LEFT, RIGHT, rswL, sx, par


def crossing(W, p, r, maxs=10 ** 7):
    tape, i = {}, -1
    for x in W:
        tape[i], tape[i - 1] = (0, 1) if x else (1, 1); i -= 2
    if p: tape[i] = 1
    if r: tape[0] = 1
    h, st, mv, lo, hi = 0, 'E' if W[0] else 'F', 0, min(tape, default=0), 0
    for t in range(maxs):
        a = T[(st, tape.get(h, 0))]
        if a is None: return ('halt',)
        if st == 'E' and mv == 1 and a[1] == -1:
            L, R = tok_left(tape, h, lo), tok_right(tape, h, hi)
            if not (LEFT.match(L) and RIGHT.match(R)) and R != 'o': return ('broken', L, R)
            if 'o' not in L[1:] and R != 'o': return ('turn', L, R)
        tape[h] = a[0]; h += a[1]; mv = a[1]; st = a[2]; lo = min(lo, h); hi = max(hi, h)
    return ('timeout',)


def runs(W):
    return [len(x) for x in ''.join('ab'[x] for x in W).split('b')]


def check_run(N):
    tape, h, st, lo, hi, mv = {}, 0, 'A', 0, 0, 0
    pending, ok, n = None, 0, 0
    for t in range(N):
        a = T[(st, tape.get(h, 0))]
        if st == 'E' and mv == 1 and a[1] == -1:
            L, R = tok_left(tape, h, lo), tok_right(tape, h, hi)
            if 'o' not in L[1:] and R != 'o':
                if pending is not None:
                    n += 1; ok += pending == ('turn', L, R); pending = None
                p = 1 if L.startswith('o') else 0
                w = [x == 'b' for x in reversed(L.lstrip('o'))]
                s = [x == 'c' for x in R[1:].rstrip('o')]
                W, e, rest = rswL(0, [0], list(reversed(sx(1, w))) + [1] + s)
                if rest is None:
                    q, rr = p ^ par(1, w), int(R.endswith('o'))
                    ru = runs(W)
                    even = [(k, ru[k]) for k in range(1, len(ru) - 1) if ru[k] % 2 == 0]
                    print(f'step {t}: |W| = {len(W)}, p = {q}, r = {rr}, first a-run {ru[0]}, last {ru[-1]}, '
                          f'even inner a-runs (index, length) {even}')
                    pending = crossing(W, q, rr)
        tape[h] = a[0]; h += a[1]; mv = a[1]; st = a[2]; lo = min(lo, h); hi = max(hi, h)
    print(f'crossing() matches the run at {ok} of {n} crossings')


def word(rs):
    return [x for k, n in enumerate(rs) for x in [False] * n + ([True] if k < len(rs) - 1 else [])]


def table():
    for firsts, lasts, mids, mb in (((0, 1, 2, 3), (0, 1, 2, 3), (1, 3, 5), 5), ((2, 3), (1, 3, 5), (1, 3, 5, 7, 9), 5)):
        C, bad = Counter(), []
        for m in range(1, mb + 1):
            for rs in itertools.product(firsts, *[mids] * (m - 1), lasts):
                W = word(rs)
                for p, r in itertools.product((0, 1), repeat=2):
                    k = crossing(W, p, r)[0]
                    C[(rs[0], rs[-1] % 2, k)] += 1
                    if k != 'turn' and len(bad) < 6: bad.append((rs, p, r))
        print('first runs', firsts, 'last runs', lasts, 'inner runs', mids, 'up to', mb, 'b:')
        for k, v in sorted(C.items()): print('   first, last mod 2, outcome', k, v)
        print('   some broken:', bad)


if __name__ == '__main__':
    if sys.argv[1:2] == ['table']: table()
    else: check_run(int(float(sys.argv[2])) if len(sys.argv) > 2 else 2 * 10 ** 7)
