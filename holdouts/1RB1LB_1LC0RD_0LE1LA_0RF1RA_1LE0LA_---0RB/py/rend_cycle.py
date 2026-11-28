"""The right end of 1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB as a closed system.

Locality (lean/Trip.lean `trip`, lean/Token.lean `trip_tok`): a round trip leaves every cell p up to the turn at
1 xor f[p] xor f[p+3], f the tape with the holes of lone 1s filled. A cell's new value depends only on cells to its right.
So for any cut P the suffix of cells P, P+1, ... changes only in three ways:

  * the trip turns left of P - 1: the suffix is untouched;
  * the trip turns at P - 1 (needs c[P-1] = c[P] = 0): only c[P] changes, to 1;
  * the trip reaches P: the suffix changes by a map that depends only on the suffix and on how the right sweep arrives
    at P. If it arrives in ordinary mode, the only outside cell that matters is c[P-1], and only when the suffix starts
    with 1 0 (a lone 1 at P iff c[P-1] = 0). Running the machine on `0 + suffix` and `011 + suffix`, from A on the
    first cell, covers both cases. If it arrives in token mode (a lone 1 left of P whose 110 words reach P), the
    prefixes 010, 0101, 01011 cover the three phases.

This script takes the last L = 100 cells (counted back from the rightmost visited cell) and closes the set of such
windows under these moves, using ordinary arrivals only. The result: 12 windows, each with a 1 at the cut (so no turn at
P - 1 can touch them), each with one successor whatever c[P-1] is, forming one cycle of 12 entries. So once the real run
holds one of them, the last 100 cells run through this cycle forever, and the right end never halts, unless a right sweep
reaches the cut in token mode. The script also lists which windows a token-mode arrival would make halt.

usage: python3 rend_cycle.py [TL_FILE]
  TL_FILE: output of `TL=100 ./trips N 0 REPORT | grep ^TL` (c/trips.c prints the last 100 cells whenever they change).
  The script then reports the first trip at which the real window is in the cycle and checks every later one.
"""
import sys
from collections import deque

TM = "1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB".split('_')
TR = {}
for i, g in enumerate(TM):
    for r in (0, 1):
        x = g[3 * r:3 * r + 3]
        TR[(i, r)] = None if x[0] == '-' else (int(x[0]), 1 if x[1] == 'R' else -1, ord(x[2]) - 65)

L = 100
START = "1111111111101111101110111111111110011111011011111001101101101111110110110110011111001111100110101111"


def entry(pre, w):
    """Run the machine on pre + w + blanks, A on the first cell, until the head leaves to the left.
    Returns (new suffix cells, rightmost head position relative to the cut), or None if it halts."""
    t = [int(c) for c in pre] + w + [0] * 8
    p, s, mx = 0, 0, 0
    while True:
        if p >= len(t):
            t += [0] * 8
        a = TR[(s, t[p])]
        if a is None:
            return None
        t[p] = a[0]
        p += a[1]
        s = a[2]
        mx = max(mx, p)
        if p < 0:
            assert s == 0
            return t[len(pre):], mx - len(pre)


def successors(st, pres):
    """Windows after one entry (for each prefix), and after a turn at P - 1 when c[P] = 0. None if a prefix halts."""
    w = [int(c) for c in st]
    out = []
    for pre in pres:
        if pre == '0' and w[0] == 0:
            continue  # that trip turns at P - 1: handled below
        r = entry(pre, w)
        if r is None:
            return None
        new, mx = r
        hi = max(L - 1, mx)
        new = (new + [0] * (hi + 1))[:hi + 1]
        out.append(''.join(map(str, new[-L:])))
    if w[0] == 0:
        out.append('1' + st[1:])
    return out


def main():
    seen = {START}
    q = deque([START])
    succ = {}
    while q:
        st = q.popleft()
        o = successors(st, ['0', '011'])
        if o is None:
            print('a window halts on an ordinary arrival:', st)
            return 1
        succ[st] = o
        for x in o:
            if x not in seen:
                seen.add(x)
                q.append(x)
    det = all(len(set(o)) == 1 for o in succ.values())
    ones = all(s[0] == '1' for s in seen)
    order, s = [], START
    while s not in order:
        order.append(s)
        s = succ[s][0]
    print(f'closed set of {len(seen)} windows of the last {L} cells; 1 at the cut in all: {ones}; '
          f'one successor each: {det}; one cycle through all: {len(order) == len(seen) and s == START}')
    for i, s in enumerate(order):
        bad = [p for p in ['010', '0101', '01011'] if successors(s, [p]) is None]
        print(f'  {i:2d} {s}' + (f'   halts if the sweep arrives in token mode (prefix {",".join(bad)})' if bad else ''))
    if len(sys.argv) > 1:
        rows = [l.split() for l in open(sys.argv[1]) if l.startswith('TL ')]
        first = next((i for i, r in enumerate(rows) if r[3] in seen), None)
        if first is None:
            print('the real window never enters the cycle in this file')
            return 1
        out = sum(1 for r in rows[first:] if r[3] not in seen)
        steps_ok = all(rows[i + 1][3] == succ[rows[i][3]][0] for i in range(first, len(rows) - 1))
        print(f'real run: window in the cycle from trip {rows[first][1]} on; {len(rows) - first} later windows, '
              f'{out} outside the set, each one the predicted successor of the one before: {steps_ok}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
