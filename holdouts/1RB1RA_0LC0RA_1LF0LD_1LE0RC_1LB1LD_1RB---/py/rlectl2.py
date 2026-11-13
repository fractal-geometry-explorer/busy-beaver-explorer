"""Closed tape language with a richer automaton state than rlectl.py.  A stream (one side of the head, read outward)
is described by
  * the near window of rlectl.py: its first K runs (lengths exact up to C1 / C0, then parity), and
  * a summary computed by a small DFA that reads the stream from its far end towards the head:
    the first J runs after the blank end (the "end zone", same length classes), then the number of *kinks* after that
    zone, capped at m (m + 1 = more), and the parity of the 1s since the last 0.  A kink is a 0 that follows an even
    number of 1s since the previous 0 (an even block, or two 0s in a row): the places where the grid of pairs slips.
push(x, state) is still a function (window push, DFA step), so the search and the check of rlectl.py apply unchanged.

usage: python3 holdouts/1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB---/py/rlectl2.py MACHINE K,C1,C0,J,m [...]
       (TMAX seconds per try, default 120; SHOWPATH=1 PATH_N=40 prints the abstract path to a halt)
"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rlectl
from rlectl import table, search


class Dom2:
    def __init__(self, K, C1, C0, J, m):
        self.K, self.C1, self.C0, self.J, self.m = K, C1, C0, J, m
        self.blank = ((), True, 'Z')

    def inc(self, sym, n):
        if sym == 1:
            if n <= self.C1: return n + 1
            return self.C1 + 1 if n == self.C1 + 2 else self.C1 + 2
        return min(n + 1, self.C0 + 1)

    def far(self, d, x):
        if d == 'Z':
            return 'Z' if x == 0 else ('P', ((1, 1),))
        if d[0] == 'P':
            runs = d[1]
            if runs[-1][0] == x:
                return ('P', runs[:-1] + ((x, self.inc(x, runs[-1][1])),))
            if len(runs) < self.J:
                return ('P', runs + ((x, 1),))
            par = runs[-1][1] % 2 if runs[-1][0] == 1 else 0
            d = ('F', runs, 0, par)
        _, pre, k, par = d
        if x == 1:
            return ('F', pre, k, par ^ 1)
        if par == 0:
            k = min(k + 1, self.m + 1)
        return ('F', pre, k, 0)

    def push(self, x, st):
        runs, closed, d = st
        if not runs and x == 0:
            return st
        d2 = self.far(d, x)
        if runs and runs[0][0] == x:
            return (((x, self.inc(x, runs[0][1])),) + runs[1:], closed, d2)
        runs = ((x, 1),) + runs
        if len(runs) > self.K:
            runs = runs[:self.K]; closed = False
        return (runs, closed, d2)


def fmtst(st):
    runs, closed, d = st
    s = ' '.join('%d^%d' % r for r in runs) + (' #' if closed else ' ..')
    if d == 'Z': return s + ' {blank}'
    if d[0] == 'P': return s + ' {end: ' + ' '.join('%d^%d' % r for r in d[1]) + '}'
    return s + ' {end: ' + ' '.join('%d^%d' % r for r in d[1]) + '; kinks %d par %d}' % (d[2], d[3])


if __name__ == '__main__':
    M = sys.argv[1]
    for arg in sys.argv[2:]:
        K, C1, C0, J, m = map(int, arg.split(','))
        t0 = time.time()
        dom = Dom2(K, C1, C0, J, m)
        ok, S, states, pops, halting = search(table(M), dom, dom, tmax=float(os.environ.get('TMAX', '120')),
                                              maxcfg=int(float(os.environ.get('MAXCFG', '3e6'))))
        print('K=%d C1=%d C0=%d J=%d m=%d: %s  cfgs %d states %d/%d  %.1fs' % (
            K, C1, C0, J, m, {True: 'CLOSED no halt', False: 'halting cfg', None: 'gave up'}[ok], len(S),
            len(states[0]), len(states[1]), time.time() - t0))
        for cfg, x in halting[:1]:
            print('   halt:', 'ABCDEF'[cfg[0]], 'reads', x, '| left:', fmtst(cfg[1]), '| right:', fmtst(cfg[2]))
            if 'SHOWPATH' in os.environ:
                path = []
                c = cfg
                while c is not None: path.append(c); c = rlectl.PARENT[c]
                for c in path[::-1][-int(os.environ.get('PATH_N', '40')):]:
                    print('      %-60s [%s] %s' % (fmtst(c[1]), 'ABCDEF'[c[0]], fmtst(c[2])))
        sys.stdout.flush()
