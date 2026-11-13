"""Closed tape language with run-length windows.  Each side of the head is a stream read outward (nearest cell first).
Abstract state of a stream = (runs, closed): the first K runs as (symbol, length class), closed = the stream is blank
after them.  Length classes of a run of 1s: 1..C1 exact, C1+1 / C1+2 = longer, with that parity.  Runs of 0s: 1..C0
exact, C0+1 = longer.  push(x, state) is a function; the automaton edge state --x--> state' exists when
push(x, state') = state for a discovered state' (as in bbtools.ctl).

Result for this machine: no certificate (K = 2..4 reach a halting abstract configuration, K = 5 gives up).
usage: python3 holdouts/1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB---/py/rlectl.py MACHINE K,C1,C0 [K,C1,C0 ...]   (SHOWPATH=1 PATH_N=40 prints the abstract path)"""
import sys, time
PARENT = {}
from collections import defaultdict, deque

def table(m):
    T = {}
    for s, part in enumerate(m.split('_')):
        for b in range(2):
            t = part[3*b:3*b+3]
            T[(s, b)] = None if t[2] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65)
    return T

class Dom:
    def __init__(self, K, C1, C0, KL=None):
        self.K, self.C1, self.C0 = K, C1, C0
        self.blank = ((), True)
    def inc(self, sym, n):
        if sym == 1:
            if n <= self.C1: return n + 1
            return self.C1 + 1 if n == self.C1 + 2 else self.C1 + 2
        return min(n + 1, self.C0 + 1)
    def push(self, x, st):
        runs, closed = st
        if runs and runs[0][0] == x:
            return (((x, self.inc(x, runs[0][1])),) + runs[1:], closed)
        if not runs and x == 0:
            return st
        runs = ((x, 1),) + runs
        if len(runs) > self.K:
            runs = runs[:self.K]; closed = False
        return (runs, closed)

def search(T, domL, domR, maxcfg=3000000, tmax=600, log=None):
    t0 = time.time()
    states = [set(), set()]           # known abstract states: left, right
    doms = [domL, domR]
    pops = [defaultdict(list), defaultdict(list)]   # state -> [(x, state')]
    S = set()
    byside = [defaultdict(list), defaultdict(list)]  # state -> configs having it on that side
    work = deque()
    halting = []
    def add_state(side, st):
        if st in states[side]: return
        states[side].add(st)
        d = doms[side]
        new = []
        for x in (0, 1):
            p = d.push(x, st)
            pops[side][p].append((x, st))
            new.append((p, (x, st)))
        # the pushed states are not added: they exist only if reached; but configs already using p get a new pop
        for p, e in new:
            for cfg in byside[side].get(p, ()):
                work.append((cfg, side, e))
    def add_cfg(cfg, par=None):
        if cfg in S: return
        S.add(cfg); PARENT[cfg] = par
        s, l, r = cfg
        add_state(0, l); add_state(1, r)
        byside[0][l].append(cfg); byside[1][r].append(cfg)
        work.append((cfg, 2, None))
    def do(cfg, redge, ledge):
        s, l, r = cfg
        x, r2 = redge
        tr = T[(s, x)]
        if tr is None:
            halting.append((cfg, x)); return
        w, d, s2 = tr
        if d == 1:
            add_cfg((s2, domL.push(w, l), r2), cfg)
        else:
            for (y, l2) in ([ledge] if ledge else list(pops[0][l])):
                mid = domR.push(w, r2)
                add_state(1, mid)
                add_cfg((s2, l2, domR.push(y, mid)), cfg)
    add_cfg((0, domL.blank, domR.blank))
    n = 0
    while work:
        cfg, side, e = work.popleft()
        n += 1
        if side == 2:
            for redge in list(pops[1][cfg[2]]): do(cfg, redge, None)
        elif side == 1:
            do(cfg, e, None)
        else:
            # a new left pop for cfg: only matters for left moves, for each right pop
            for redge in list(pops[1][cfg[2]]):
                tr = T[(cfg[0], redge[0])]
                if tr is not None and tr[1] == -1: do(cfg, redge, e)
        if halting: break
        if len(S) > maxcfg or (n % 20000 == 0 and time.time() - t0 > tmax): return None, S, states, pops, halting
        if log and n % 200000 == 0: log("  %d items, %d cfgs, %d/%d states, %.0fs" % (n, len(S), len(states[0]), len(states[1]), time.time()-t0))
    return (not halting), S, states, pops, halting

def fmtst(st):
    runs, closed = st
    return ' '.join('%d^%d' % r for r in runs) + (' #' if closed else ' ..')

if __name__ == '__main__':
    M = sys.argv[1]
    for arg in sys.argv[2:]:
        K, C1, C0 = map(int, arg.split(','))
        t0 = time.time()
        ok, S, states, pops, halting = search(table(M), Dom(K, C1, C0), Dom(K, C1, C0), tmax=float(__import__('os').environ.get('TMAX', '120')))
        print('K=%d C1=%d C0=%d: %s  cfgs %d states %d/%d  %.1fs' % (K, C1, C0, {True: 'CLOSED no halt', False: 'halting cfg', None: 'gave up'}[ok], len(S), len(states[0]), len(states[1]), time.time() - t0))
        for cfg, x in halting[:3]:
            print('   halt:', 'ABCDEF'[cfg[0]], 'reads', x, '| left:', fmtst(cfg[1]), '| right:', fmtst(cfg[2]))
            if 'SHOWPATH' in __import__('os').environ:
                path = []
                c = cfg
                while c is not None: path.append(c); c = PARENT[c]
                for c in path[::-1][-int(__import__('os').environ['PATH_N']):]: print('      %-40s [%s] %s' % (fmtst(c[1]), 'ABCDEF'[c[0]], fmtst(c[2])))
                break
        sys.stdout.flush()
