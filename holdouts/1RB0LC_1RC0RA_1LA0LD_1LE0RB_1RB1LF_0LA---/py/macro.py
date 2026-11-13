"""The machine between visits of state A: an exhaustive case split.

From a configuration in state A, run the machine until it is in state A again, branching on every cell it reads
that is not yet fixed.  The tree is finite: A reading 0 gives R1 and R2 (R2 for every number of ones erased, here
up to MAXK); A reading 1 gives seven cases by the cells on its left: 00 (L5), 10 (L1), 001 (L8), 00101 (L6),
10101 (L2), 1101 (L4, the halt) and 11, which leads to state A reading 1 one cell to the right with a 0 on its left,
that is to L1 or L5 (the two compositions are L3 and L7).  These are the theorems of lean/Rules.lean; the split
shows that no case is missing and that L4 is the only halt.
"""
import sys
from engine import T

MAXK = 12


def sim(W, X, head):
    """W: cells left of the head (nearest last), X: right of it; the head reads `head` in state A."""
    n = len(W); tape = list(W) + [head] + list(X); h = n; st = 'A'; steps = 0
    while True:
        if h < 0: return ('needL',)
        if h >= len(tape): return ('needR',)
        if steps and st == 'A':
            return ('A', h, tape, steps)
        tr = T[(st, tape[h])]
        if tr is None: return ('halt', h, tape, steps)
        w, d, st = tr
        tape[h] = w; h += d; steps += 1


def split(head):
    out = []
    def rec(W, X):
        r = sim(W, X, head)
        if r[0] == 'needR':
            if len(X) > MAXK: return
            for b in (0, 1): rec(W, X + [b])
        elif r[0] == 'needL':
            for b in (0, 1): rec([b] + W, X)
        else:
            out.append((W, X, r))
    rec([], [])
    return out


S = lambda l: ''.join(map(str, l))
if __name__ == '__main__':
    lines = []
    for head in (0, 1):
        for W, X, r in split(head):
            h, t = r[1], r[2]
            lines.append(f'{S(W)} A>{head} {S(X)}'.strip() + '  ->  ' +
                         (f'{S(t[:h])} A>{S(t[h:h+1])} {S(t[h+1:])}'.strip() if r[0] == 'A' else 'HALT (F reads 1)')
                         + f'   [{r[3]} steps]')
    print('\n'.join(lines))
    halts = [l for l in lines if 'HALT' in l]
    assert halts == ['1101 A>1  ->  HALT (F reads 1)   [4 steps]'], halts
    assert len([l for l in lines if ' A>1' in l.split('->')[0]]) == 7
    print(f'{len(lines)} cases; the only halt: 1101 A>1')
