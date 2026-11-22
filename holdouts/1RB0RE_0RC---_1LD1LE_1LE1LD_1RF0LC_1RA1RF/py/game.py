"""The near side of a crossing on its own, with the far part left free (Window.lean, README "Windows").

During a crossing (`T2 N O p s r`) the near part N, the frozen word s and the end bit r evolve without looking at the
far part O, except that after each odd bounce (`par true N` true) the far part's first u and the v's after it
become a's at the far end of N: `2 + 2z` of them for a run `u v^z`.  So the near side is a game in which the far part
picks z.  This program lets z range over 0..Z (and lets the crossing end at any odd bounce) and searches breadth-first
for a failure of `astep` (F on the blank end during a crossing).

  python3 game.py Z DEPTH M        start at crossing starts N = a^m (m in the digits of M), s empty, r = 1
  python3 game.py Z DEPTH N s      start at the crossing turn with near part N and frozen word s (bits), r = 0

Both find failures (for example Z = 3, DEPTH = 14, M = 123; or Z = 2, DEPTH = 13 from N = 101010000, s = 010110010,
a state of the run two bounces after E read the last 1).  So no proof can treat the far part as arbitrary: it is the
run lengths of the far part that keep the near part short.
"""
import sys
from collections import deque
from turnshape import sx, par, rswL


def succ(st, Z):
    N, s, r, mode = st
    q = par(1, list(N))
    tail = [] if mode == 'EO' else [1] + list(s)
    rr = 0 if mode == 'EO' else r
    W2, e2, rest = rswL(0, [], list(reversed(sx(1, list(N)))) + tail)
    if rest is not None:
        base = (tuple(W2), tuple(rest), rr, 'T2')
    elif not e2 and not rr:
        return ['FAIL']
    elif e2 and rr:
        base = (tuple(W2), (), 0, 'EO')
    else:
        base = (tuple([0] + W2), (), 1, 'T2')
    if q:
        return [(base[0] + (0,) * (2 + 2 * z),) + base[1:] for z in range(Z + 1)]
    return [base]


def search(starts, Z, depth):
    par_ = {s: None for s in starts}
    dq = deque((s, 0) for s in starts)
    fails = []
    while dq:
        st, d = dq.popleft()
        if d >= depth: continue
        for o in succ(st, Z):
            if o == 'FAIL':
                path = []
                while st is not None: path.append(st); st = par_[st]
                fails.append(path[::-1]); break
            if o not in par_: par_[o] = st; dq.append((o, d + 1))
        if fails: break
    return len(par_), fails


if __name__ == '__main__':
    Z, depth = int(sys.argv[1]), int(sys.argv[2])
    if len(sys.argv) > 4:
        starts = [(tuple(map(int, sys.argv[3])), tuple(map(int, sys.argv[4])), 0, 'T2')]
    else:
        starts = [((0,) * int(m), (), 1, 'T2') for m in sys.argv[3]]
    n, fails = search(starts, Z, depth)
    print(n, 'states searched;', 'a failure:' if fails else 'no failure')
    for p in fails[:1]:
        for N, s, r, mode in p:
            print('  ', mode, 'N =', ''.join(map(str, N)), 's =', ''.join(map(str, s)) or 'empty', 'r =', r)
