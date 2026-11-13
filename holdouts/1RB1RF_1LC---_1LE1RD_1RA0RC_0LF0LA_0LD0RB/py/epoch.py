"""The epoch map of 1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB: from `1 A>0 0 1^N` (state A, moving right) run until
the next configuration of that form, `1 A>0 0 1^N'`, or a halt.  f(N) = N' or None (halt).

usage: python3 epoch.py N ...             f(N) and the steps
       python3 epoch.py scan 1 3000       every N in the range: the ones that halt
       python3 epoch.py plain N ...       the same with the plain simulator bbtools.machine (slow; a check)
"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from turnacc import TurnAcc
from run import M, WORDS, is_epoch


class _Found(Exception):
    pass


def f(N, maxsteps=10 ** 60):
    A = TurnAcc(M, WORDS, tokens=[['1', 1], ['0', 1], ['0', 1], ['1', N]], state=0, head=1, dir=1)

    def on(a, j):
        if is_epoch(a.s):
            raise _Found(sum(n for w, n in a.s.tok if w == '1') - 1)
    try:
        r = A.run(maxsteps, on)
    except _Found as e:
        return e.args[0], A.s.steps
    return (None if r == 'halt' else 'max'), A.s.steps


def plain(N, maxsteps=10 ** 9):
    sys.path.insert(0, os.path.join(HERE, '..', '..', '..', 'tools', 'py'))
    from bbtools.machine import Machine
    m = Machine.parse(M)
    t = {0: 1}
    for i in range(N):
        t[3 + i] = 1
    h, q, n = 1, 0, 0
    while n < maxsteps:
        b = t.get(h, 0)
        tr = m.table[q][b]
        if tr is None:
            return None, n + 1
        w, mv, q2 = tr
        t[h] = w; h += mv; q = q2; n += 1
        if q == 0 and mv == 1 and t.get(h, 0) == 0 and t.get(h + 1, 0) == 0 and t.get(h - 1, 0) == 1:
            ones = [i for i, v in t.items() if v]
            lo = min(ones)
            if lo == h - 1 and sorted(ones) == [h - 1] + list(range(h + 2, h + 2 + len(ones) - 1)):
                return len(ones) - 1, n
    return 'max', n


if __name__ == '__main__':
    if sys.argv[1] == 'scan':
        lo, hi = int(sys.argv[2]), int(sys.argv[3])
        hs = [N for N in range(lo, hi + 1) if f(N)[0] is None]
        print(len(hs), 'halting N in', lo, '..', hi, ':', hs)
    elif sys.argv[1] == 'plain':
        for N in map(int, sys.argv[2:]):
            print(N, plain(N), f(N))
    else:
        for N in map(int, sys.argv[1:]):
            print(N, f(N))
