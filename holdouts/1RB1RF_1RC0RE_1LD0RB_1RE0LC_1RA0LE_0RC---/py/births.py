"""Births of 1RB1RF_1RC0RE_1LD0RB_1RE0LC_1RA0LE_0RC---: every time the end block is used up, the last separator turns
into a new cursor and the cursor that was active is left where it stands.  Where it is left decides what later
cursors meet, so this lists, for each birth of the run from blank tape, the cells around the cursor left behind.

usage: python3 births.py STEPS [all]     # e.g. 1e17 (about 6 s); `all` prints every birth, not only the counts

Kinds:  mid-block   a^k c a^m     the cursor stands inside a block (the usual case)
        after-b     b c a^m       the cursor was about to cross a separator
        mid-hop     0 a 1 1 a b   the cursor was half way across a separator (`hop0a` done, `hop0b` not)
        other       anything else (printed in full)
The last line counts the visits at which two or three cursor cells 1 stand side by side (three, left behind by a
birth, is the tape of lean/Escape.lean).  Uses the accelerated simulator qsim.py (validated against plain simulation, jumps not proved).
"""
import sys
from collections import Counter
from qsim import Sim, Halt


def item(x):
    if type(x) is int: return str(x)
    if x[0] == 'w': return ('a' if x[1] == '01' else 'A') + ('^%d' % x[2] if x[2] > 1 else '')
    if x[0] == 'b': return 'b'
    return '(b a^%d)^%d' % (x[1], x[2])


def kind(L):
    """L ends with the new cursor `0 a 1`; classify the nearest single cell to its left."""
    i = len(L) - 4
    while i >= 0 and type(L[i]) is not int: i -= 1
    if i <= 0: return 'none', ''
    ctx = ' '.join(item(x) for x in L[max(0, i - 4):i + 3])
    left = L[i - 1]; right = L[i + 1] if i + 1 < len(L) else None
    if type(left) is int or type(right) is int:
        cells = [x for x in L[max(0, i - 4):i + 4]]
        txt = ' '.join(item(x) for x in cells)
        return ('mid-hop' if '0 a 1 1 a' in txt else 'other'), ctx
    if left[0] == 'w': return 'mid-block', ctx
    if left[0] == 'b' or (left[0] == 'S' and left[1] == 0): return 'after-b', ctx
    if left[0] == 'S': return 'mid-block', ctx
    return 'other', ctx


if __name__ == "__main__":
    N = float(sys.argv[1]); show = len(sys.argv) > 2
    s = Sim(); c = Counter(); nb = 0; pairs = triples = visits = 0
    try:
        while s.steps < N:
            s.trip(); s.sample(); s.check_pending()
            L = s.L; visits += 1
            ones = [type(x) is int and x == 1 for x in L[1:]]
            p2 = any(ones[i] and ones[i + 1] for i in range(len(ones) - 1))
            pairs += p2
            triples += p2 and any(ones[i] and ones[i + 1] and ones[i + 2] for i in range(len(ones) - 2))
            if s.pending is None and len(L) >= 3 and L[-1] == 1 and L[-2] == ('w', '01', 1) and L[-3] == 0:
                nb += 1; k, ctx = kind(L); c[k] += 1
                if show or k in ('mid-hop', 'other'): print('birth %d at step %.4e: %s   [... %s ...]' % (nb, s.steps, k, ctx))
            s.try_jump()
    except Halt:
        print('HALT at step', s.steps + 1)
    print('%d births in %.3e steps:' % (nb, s.steps), dict(c))
    print('of the %d visits of the right end simulated one by one: %d with two cursor cells 1 side by side, %d with three'
          % (visits, pairs, triples))
