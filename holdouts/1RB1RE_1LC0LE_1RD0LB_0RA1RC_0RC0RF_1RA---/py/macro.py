"""The machine as a rewriting system on two stacks (the rules of lean/Macro.lean), and checks against the plain machine.

A configuration is (left, mode, right): `left` is the tape left of the head (last item nearest), `right` the tape
from the head on (first item nearest, blank beyond).  Modes A, C, D read the right tape; mode B stands on the last
cell of `left` and reads it and its left neighbour.

    A> 00 -> <B 01    A> 01 -> 01 A>    A> 10 -> 10 C>    A> 110 -> 101 A>    A> 111 halts
    C> 0 -> 1 D>      C> 1 -> <B 0      D> 0 -> 0 A>      D> 1 -> 1 C>
    10 <B -> <B 01    00 <B -> 11 C>    01 <B -> 01 D>    11 <B -> 01 A>

An *excursion* starts with A on blank tape at the right end of a word w and ends the next time that is so.

usage: python3 macro.py check N        # all words w of length <= N: the excursion by these rules and by the plain
                                       # machine end with the same tape, and neither halts
       python3 macro.py show RUNS      # one excursion, rule by rule; RUNS is a list of runs of 1s, e.g. "3 2 1 1 2"
       python3 macro.py depth LEN TRIALS [SEED]   # random words: how far left the head goes in one excursion
"""
import random
import sys
from collections import Counter

M = "1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA---"


def parse(m):
    T = {}
    for i, row in enumerate(m.split('_')):
        for s in range(2):
            t = row[3 * s:3 * s + 3]
            T[(i, s)] = None if t[0] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65)
    return T


def mstep(L, m, R):
    """One rule, in place on the lists L and R; returns the new mode or 'HALT'."""
    def r(i):
        return R[i] if i < len(R) else 0
    if m == 'B':
        b = L.pop() if L else 0
        c = L.pop() if L else 0
        if (c, b) == (1, 0): R[:0] = [0, 1]; return 'B'
        if (c, b) == (0, 0): L += [1, 1]; return 'C'
        L += [0, 1]
        return 'D' if c == 0 else 'A'
    if m == 'C':
        if r(0) == 0: del R[:1]; L.append(1); return 'D'
        R[0] = 0; return 'B'
    if m == 'D':
        x = r(0); del R[:1]; L.append(x)
        return 'C' if x else 'A'
    if (r(0), r(1)) == (0, 0): del R[:2]; R[:0] = [0, 1]; return 'B'
    if (r(0), r(1)) == (0, 1): del R[:2]; L += [0, 1]; return 'A'
    if (r(0), r(1)) == (1, 0): del R[:2]; L += [1, 0]; return 'C'
    if r(2) == 0: del R[:3]; L += [1, 0, 1]; return 'A'
    return 'HALT'


def excursion(w, trace=None):
    """From `w A>` on blank tape to the next such configuration: (final word or 'HALT', deepest cell read, rules used)."""
    L = list(w); R = []; m = 'A'; n = 0; low = len(L)
    while True:
        m = mstep(L, m, R)
        if m == 'HALT': return 'HALT', len(w) - low, n
        n += 1
        while R and R[-1] == 0: R.pop()
        low = min(low, len(L) - (1 if m == 'B' else 0))
        if trace is not None: trace.append((list(L), m, list(R)))
        if m == 'A' and not R: return L, len(w) - low, n


def plain(w, maxs=10 ** 7):
    """The same excursion on the plain machine."""
    T = parse(M)
    left = list(w); right = []; s = 0
    for _ in range(maxs):
        x = right.pop() if right else 0
        tr = T[(s, x)]
        if tr is None: return 'HALT'
        if tr[1] == 1: left.append(tr[0])
        else:
            right.append(tr[0]); right.append(left.pop() if left else 0)
        s = tr[2]
        while right and right[0] == 0: right.pop(0)
        if s == 0 and not right: return left
    return 'LONG'


def strip(x):
    if isinstance(x, str): return x
    x = list(x)
    while x and x[0] == 0: x.pop(0)
    return x


def runs(cells):
    return ' '.join(str(len(x)) for x in ''.join(map(str, cells)).split('0'))


if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == 'check':
        N = int(sys.argv[2]); bad = halts = cnt = 0
        for n in range(N + 1):
            for bits in range(2 ** n):
                w = [(bits >> i) & 1 for i in range(n)]
                if n and w[0] == 0: continue
                cnt += 1
                a = excursion(w)[0]; b = plain(w)
                halts += a == 'HALT' or b == 'HALT'
                bad += strip(a) != strip(b)
        print('%d words of length <= %d: %d differences between the rules and the plain machine, %d halts' % (cnt, N, bad, halts))
        sys.exit(1 if bad or halts else 0)
    if cmd == 'show':
        w = [int(c) for c in '0'.join('1' * int(x) for x in sys.argv[2].split())]
        tr = []
        res = excursion(w, tr)
        print(''.join(map(str, w)), 'A>')
        for L, m, R in tr:
            l = ''.join(map(str, L)); r = ''.join(map(str, R))
            print((l[:-1] + '[' + l[-1:] + ']B ' + r) if m == 'B' else (l + ' ' + m + '> ' + r))
        print('runs:', runs(w), ' -> ', runs(res[0]) if res[0] != 'HALT' else 'HALT')
    if cmd == 'depth':
        n = int(sys.argv[2]); random.seed(int(sys.argv[4]) if len(sys.argv) > 4 else 1); c = Counter()
        for _ in range(int(sys.argv[3])):
            w = [1] + [random.randint(0, 1) for _ in range(n - 1)]
            res, d, k = excursion(w)
            c['HALT' if res == 'HALT' else d] += 1
        print('cells read left of the right end -> number of words:', sorted(c.items(), key=lambda t: (isinstance(t[0], str), t[0])))
