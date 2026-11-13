"""Charged pairs in the counter model of 1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB--- (model.py).

Two neighbouring groups (d, n), (d', n') are *neutral* when n = d' + 2 (mod 3) and *charged* otherwise.  A plain
decrement keeps n - d' (mod 3) for every pair, and so do the merges, so a charge stays on its group until that
group runs out.  In a neutral pair an empty group is followed by a digit 1 (the two merge); every halting pattern
starts with an empty group followed by a digit 0, so a halt needs a charged pair (lean/Charge.lean,
`good_not_halt`).  `good` below is the Lean definition: every pair neutral, except behind the empty groups that
the end-of-round events leave at the end of the list.

A charged pair is made at the end of a round when n0 + d1 = 1 (mod 3) fails, and that relation can only break
when the first group runs out and merges into the front block.

    python3 py/charge.py exhaust [D N K]   # every list of up to K groups, digits < D, blocks < N (default 3 5 6):
                                           #   good -> no halt;  good and n0 + d1 = 1 -> the next state is good,
                                           #   and keeps n0 + d1 = 1 unless the first group was (0,0) or (1,0)
                                           #   (an empty first group that merges into the front block)
    python3 py/charge.py run ROUNDS        # the run from blank tape: where the relation breaks, where charged
                                           #   pairs appear, and the lifetimes around them at the end
"""
import itertools
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from model import START, bounce_lean, jump


def pair_ok(a, b):
    return (a[1] - b[0] - 2) % 3 == 0


def tail_free(G):
    if len(G) <= 1:
        return True
    d, n = G[1]
    if n != 0:
        return False
    if len(G) == 2:
        return d <= 1
    return len(G) == 3 and d == 0 and G[2] == (0, 0)


def good(G):
    """lean/Charge.lean, `good`."""
    for i in range(len(G)):
        if tail_free(G[i:]):
            return True
        if i + 1 < len(G) and not pair_ok(G[i], G[i + 1]):
            return False
    return True


def n0rel(n0, G):
    return not G or (n0 + G[0][0]) % 3 == 1


def charges(G):
    """[(index, residue)] of the charged pairs, the free tail left out."""
    out = []
    for i in range(len(G) - 1):
        if tail_free(G[i:]):
            break
        if not pair_ok(G[i], G[i + 1]):
            out.append((i, (G[i][1] - G[i + 1][0] - 2) % 3))
    return out


def exhaust(D, N, K):
    grp = [(d, n) for d in range(D) for n in range(N)]
    tot = bad = 0
    for k in range(K + 1):
        for G in itertools.product(grp, repeat=k):
            G = list(G)
            if not good(G):
                continue
            for n0 in range(3):
                tot += 1
                r = bounce_lean(n0, G)
                if r[0] == 'halt':
                    bad += 1
                    print('HALT from a good list:', n0, G)
                    continue
                if not n0rel(n0, G) or any(d > 2 for d, _ in G):
                    continue
                if not good(r[2]):
                    bad += 1
                    print('good is lost:', n0, G, r)
                elif not n0rel(r[1], r[2]) and G[0] not in ((0, 0), (1, 0)):
                    bad += 1
                    print('the relation is lost though the first group does not merge:', n0, G, r)
    print('%d good states (digits < %d, blocks < %d, up to %d groups): %s' % (
        tot, D, N, K, 'all three claims hold' if bad == 0 else '%d FAILURES' % bad))


def lg(n):
    return '%.2f' % math.log10(n) if n > 0 else '-inf'


def run(rounds_max):
    s, rounds, rel, ch = START, 0, True, ()
    while rounds < rounds_max:
        _, n0, G = jump(*s)
        if rel and G and G[0] in ((0, 0), (1, 0)):
            print('round %d: the first group runs out and merges into the front block (%d groups)' % (rounds, len(G)))
        r = bounce_lean(n0, G)
        if r[0] != 'next':
            print('HALT in round', rounds)
            return
        s = (r[1], r[2])
        if r[3] in ('A', 'F'):
            print('round %d: event %s, %d groups' % (rounds, r[3], len(s[1])))
        if n0rel(*s) != rel:
            rel = not rel
            print('round %d: n0 + d1 = 1 (mod 3) %s' % (rounds, 'holds again' if rel else 'BREAKS'))
        if r[3] == 'E':
            rounds += 1
        c = tuple(o for _, o in charges(s[1]))
        if c != ch:
            ch = c
            print('round %d: charged pairs: %s' % (rounds, ', '.join(
                'residue %d at index %d of %d' % (o, i, len(s[1])) for i, o in charges(s[1])) or 'none'))
    n0, G = s
    while G and G[-1] == (0, 0):          # the empty group that the end of the round appended
        G = G[:-1]
    m = len(G)
    print('after %d rounds: %d groups, good = %s' % (rounds, m, good(G)))
    for i, o in charges(G):
        print('charged group at index %d (position %d from the right, residue %d); lifetimes around it:' % (i, m - i, o))
        print('  index  position  log10(block)  log10(rounds left at 3^(position-1) per round)')
        for j in range(max(0, i - 3), min(m, i + 4)):
            n, p = G[j][1], m - j
            print('  %5d  %8d  %12s  %s%s' % (j, p, lg(n), lg(n) if n == 0 else '%.2f' % (math.log10(n) - (p - 1) * math.log10(3)),
                                              '   <- charged' if j == i else ''))


if __name__ == '__main__':
    if sys.argv[1] == 'exhaust':
        a = [int(x) for x in sys.argv[2:]] or [3, 5, 6]
        exhaust(*a)
    else:
        run(int(sys.argv[2]))
