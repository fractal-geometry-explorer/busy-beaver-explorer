"""Closed tape languages that may forget the word: satctl.py with labelled cells and a "forget the right side" move.

Cells carry a label for the analysis only (the machine does not see it): s (structure: written while the head was
left of every word cell), v (a word cell the head has visited) and u (an unvisited word cell, content unknown: it
stands for both 0 and 1).  The left automaton reads letters 0s 1s 0v 1v, the right one 0s 1s 0v 1v u; right state
0 loops on u, so it accepts every right half: "forgetting" a configuration (q, l, r) means replacing it by
(q, l, 0), which contains it.  The unknowns: the automata, the set s of abstract configurations, and for each
configuration a choice forget(q, l, r): either every step from it lands in s again (and none halts), or (q, l, 0)
is in s.  A head cell u is read as 0 or 1, both followed; a cell written over a v or u cell is labelled v, over an
s cell s.

The start is the blank tape with an explicit prefix: `--start STATE PREFIX` puts the head in STATE on the first
cell of PREFIX (s-labelled), u to the right of it, 0s to the left (left state 0 loops on 0s).  Default: A on the
blank tape, every cell s (right state 0 must then also loop on 0s - not allowed - so give a prefix and start late).

Soundness: the projection (labels erased, u read as both symbols) of the abstract set is closed under steps of the
machine; see `verify`.

usage: python3 tools/py/satctl_forget.py MACHINE nL nR STATE PREFIX [dd|nn]
       PREFIX: cells from the head to the right, e.g. 1111 0; the rest u
"""
import json
import sys
import time

from pysat.formula import IDPool
from pysat.solvers import Cadical153

LL = 4                      # 0s 1s 0v 1v
LR = 5                      # ... u
VAL = [0, 1, 0, 1, None]
LAB = ["s", "s", "v", "v", "u"]


def parse(m):
    T = {}
    for qi, part in enumerate(m.split('_')):
        for b in (0, 1):
            tr = part[3 * b:3 * b + 3]
            T[(qi, b)] = None if tr[0] in '-H' else (int(tr[0]), tr[1], 'ABCDEF'.index(tr[2]))
    return T


def wletter(w, c):
    """The left/right letter of a cell written with w over a cell with letter c."""
    return w if LAB[c] == "s" else 2 + w


def build(m, nL, nR, q0, prefix, nfa=False, lprefix=(), wall=False):
    T = parse(m)
    pool = IDPool()
    cl = []
    dL = lambda i, c, j: pool.id(('dL', i, c, j))   # noqa: E731
    dR = lambda i, c, j: pool.id(('dR', i, c, j))   # noqa: E731
    s = lambda q, l, r: pool.id(('s', q, l, r))     # noqa: E731
    F = lambda q, l, r: pool.id(('F', q, l, r))     # noqa: E731
    for (n, d, A) in ((nL, dL, LL), (nR, dR, LR)):
        for i in range(n):
            for c in range(A):
                cl.append([d(i, c, j) for j in range(n)])
                if not nfa:
                    for j in range(n):
                        for k in range(j + 1, n):
                            cl.append([-d(i, c, j), -d(i, c, k)])
    if wall:                        # left state 0 is a wall: nothing leads into it, a pop from it is an exit
        for i in range(nL):
            for c in range(LL):
                cl.append([-dL(i, c, 0)])
    else:
        cl.append([dL(0, 0, 0)])    # far left: 0s
    cl.append([dR(0, 4, 0)])        # far right: u
    # the start: right state after reading the prefix from the far end (u^inf, then the prefix reversed)
    cells = list(reversed(prefix))
    x = lambda i, j: pool.id(('x', i, j))           # noqa: E731
    cl.append([x(0, 0)])
    for i, c in enumerate(cells):
        for j in range(nR):
            for k in range(nR):
                cl.append([-x(i, j), -dR(j, c, k), x(i + 1, k)])
    y = lambda i, j: pool.id(('y', i, j))           # noqa: E731
    cl.append([y(0, 0)])
    for i, c in enumerate(lprefix):
        for j in range(nL):
            for k in range(nL):
                cl.append([-y(i, j), -dL(j, c, k), y(i + 1, k)])
    for k in range(nR):
        for j in range(nL):
            cl.append([-x(len(cells), k), -y(len(lprefix), j), s(q0, j, k)])
    for q in range(6):
        for l in range(nL):
            cl.append([-F(q, l, 0)])
            for r in range(nR):
                cl.append([-s(q, l, r), -F(q, l, r), s(q, l, 0)])
    for q in range(6):
        for c in range(LR):
            for b in ((0, 1) if VAL[c] is None else (VAL[c],)):
                tr = T[(q, b)]
                P = lambda l, rp: pool.id(('P', q, c, b, l, rp))   # noqa: E731
                for l in range(nL):
                    for r in range(nR):
                        for rp in range(nR):
                            cl.append([-s(q, l, r), F(q, l, r), -dR(rp, c, r), P(l, rp)])
                if tr is None:
                    for l in range(nL):
                        for rp in range(nR):
                            cl.append([-P(l, rp)])
                    continue
                w, dirn, q2 = tr
                wl = wletter(w, c)
                if dirn == 'R':
                    for l in range(nL):
                        for rp in range(nR):
                            for l2 in range(nL):
                                cl.append([-P(l, rp), -dL(l, wl, l2), s(q2, l2, rp)])
                else:
                    Y = lambda l, r2: pool.id(('Y', q, c, b, l, r2))   # noqa: E731
                    for l in range(nL):
                        for rp in range(nR):
                            for r2 in range(nR):
                                cl.append([-P(l, rp), -dR(rp, wl, r2), Y(l, r2)])
                    Z = lambda lp, cc, r2: pool.id(('Z', q2, lp, cc, r2))  # shared by every (q, c, b) into q2
                    for l in range(nL):
                        for r2 in range(nR):
                            for lp in range(nL):
                                for cc in range(LL):
                                    cl.append([-Y(l, r2), -dL(lp, cc, l), Z(lp, cc, r2)])
    for q2 in range(6):
        for lp in range(nL):
            for cc in range(LL):
                for r2 in range(nR):
                    z = pool.id(('Z', q2, lp, cc, r2))
                    for r3 in range(nR):
                        cl.append([-z, -dR(r2, cc, r3), s(q2, lp, r3)])
    return pool, cl


def solve(m, nL, nR, q0, prefix, nfa=False, lprefix=(), wall=False):
    pool, cl = build(m, nL, nR, q0, prefix, nfa, lprefix, wall)
    S = Cadical153(bootstrap_with=cl)
    if not S.solve():
        return None
    model = set(x for x in S.get_model() if x > 0)
    get = lambda *a: pool.id(a) in model    # noqa: E731
    DL = [[[j for j in range(nL) if get('dL', i, c, j)] for c in range(LL)] for i in range(nL)]
    DR = [[[j for j in range(nR) if get('dR', i, c, j)] for c in range(LR)] for i in range(nR)]
    return DL, DR


def verify(m, DL, DR, q0, prefix):
    """Least set from the start, forgetting a configuration only when it cannot be closed: here simply follow every
    step and forget whenever a halt is enabled or ... (we forget nothing, but allow (q,l,0) as an over-approx):
    explore all steps; a halting step is fatal unless the configuration is replaced by (q,l,0), which is explored
    too.  Returns (ok, size)."""
    T = parse(m)
    nL, nR = len(DL), len(DR)
    assert 0 in DL[0][0] and 0 in DR[0][4]
    predR = {(r, c): [rp for rp in range(nR) if r in DR[rp][c]] for r in range(nR) for c in range(LR)}
    predL = {l: [(lp, c) for lp in range(nL) for c in range(LL) if l in DL[lp][c]] for l in range(nL)}
    starts = {0}
    for c in reversed(prefix):
        starts = {k for j in starts for k in DR[j][c]}
    todo = [(q0, 0, r) for r in starts]
    seen = set(todo)

    def succ(q, l, r):
        out = []
        for c in range(LR):
            for rp in predR[(r, c)]:
                for b in ((0, 1) if VAL[c] is None else (VAL[c],)):
                    tr = T[(q, b)]
                    if tr is None:
                        return None
                    w, d, q2 = tr
                    wl = wletter(w, c)
                    if d == 'R':
                        out += [(q2, l2, rp) for l2 in DL[l][wl]]
                    else:
                        out += [(q2, lp, r3) for (lp, cc) in predL[l] for r2 in DR[rp][wl] for r3 in DR[r2][cc]]
        return out
    forgot = 0
    while todo:
        q, l, r = todo.pop()
        nx = succ(q, l, r)
        if nx is None:
            if r == 0:
                return False, ('halt', q, l, r)
            nx = [(q, l, 0)]
            forgot += 1
        for y in nx:
            if y not in seen:
                seen.add(y)
                todo.append(y)
    return True, len(seen), forgot


if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('m'); ap.add_argument('nL', type=int); ap.add_argument('nR', type=int)
    ap.add_argument('state'); ap.add_argument('prefix')
    ap.add_argument('--nfa', action='store_true')
    ap.add_argument('--left', default='', help='s-cells left of the head, far end first')
    ap.add_argument('--wall', action='store_true', help='half tape: stepping left of the left cells is an exit')
    a = ap.parse_args()
    m, nL, nR, q0 = a.m, a.nL, a.nR, 'ABCDEF'.index(a.state)
    prefix = [int(ch) for ch in a.prefix.replace(" ", "")]
    lpre = [int(ch) for ch in a.left.replace(" ", "")]
    nfa = a.nfa
    t = time.time()
    res = solve(m, nL, nR, q0, prefix, nfa, lpre, a.wall)
    if res is None:
        print(m, nL, nR, 'UNSAT', round(time.time() - t, 1))
        sys.exit(1)
    DL, DR = res
    print(m, nL, nR, 'SAT', round(time.time() - t, 1), 'unverified' if (lpre or a.wall) else verify(m, DL, DR, q0, prefix))
    print(json.dumps({'DL': DL, 'DR': DR, 'q0': q0, 'prefix': prefix}))
