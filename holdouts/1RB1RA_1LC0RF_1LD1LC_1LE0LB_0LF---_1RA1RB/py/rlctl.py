"""Closed tape language from windows of M runs (run-length abstracted): search + check.
A side's state is the tuple of its last M runs, far end first: (bit, cls); cls = exact size up to cap, then 'o'/'e'.
'#' as the first item = blank from there on."""
import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../tools/py"))
from bbtools.machine import Machine, STATES

class Side:
    def __init__(self, M, cap1, cap0):
        self.M, self.cap = M, {1: cap1, 0: cap0}
        self.states = [("#",)]
        self.index = {("#",): 0}
        self.edges = set()      # (near state, bit, far state)
        self.acc = [0]
        self._pops = {}
    def inc(self, b, c):
        cap = self.cap[b]
        if isinstance(c, int):
            if c < cap: return c + 1
            return 'o' if (c + 1) % 2 else 'e'
        return 'e' if c == 'o' else 'o'
    def push(self, q, x):
        """state after adding cell x on the near side; creates it if new. returns (index, isnew)"""
        w = self.states[q]
        if w == ("#",) and x == 0:
            return q, False
        if w[-1] != "#" and w[-1][0] == x:
            n = w[:-1] + ((x, self.inc(x, w[-1][1])),)
        else:
            n = w + ((x, 1),)
            if len(n) > self.M:
                n = n[len(n) - self.M:]
        new = n not in self.index
        if new:
            self.index[n] = len(self.states); self.states.append(n)
        j = self.index[n]
        e = (j, x, q)
        if e not in self.edges:
            self.edges.add(e); self._pops.setdefault(j, []).append((x, q)); new = True
        return j, new
    def pops(self, q):
        out = list(self._pops.get(q, []))
        if q == 0: out.append((0, 0))
        return out
    def preds(self, q, x):
        return [a for (a, y, b) in self.edges if b == q and y == x]

def search(mtext, M, cap1, cap0, limit=2000000, verbose=False):
    m = Machine.parse(mtext)
    L, R = Side(M, cap1, cap0), Side(M, cap1, cap0)
    S = {(0, 0, 0)}
    while True:
        changed = False
        for (s, ql, qr) in list(S):
            for x, qr2 in R.pops(qr):
                t = m.table[s][x]
                if t is None: continue
                w, d, s2 = t
                if d == 1:
                    j, new = L.push(ql, w); changed |= new
                    n = (s2, j, qr2)
                    if n not in S: S.add(n); changed = True
                else:
                    j1, new = R.push(qr2, w); changed |= new
                    for y, ql2 in L.pops(ql):
                        j0, new = R.push(j1, y); changed |= new
                        n = (s2, ql2, j0)
                        if n not in S: S.add(n); changed = True
        if verbose: print(len(S), len(L.states), len(R.states), file=sys.stderr)
        if len(S) > limit: return None
        if not changed: break
    return m, L, R, S

def halting(m, R, S):
    return [(s, ql, qr, x) for (s, ql, qr) in S for x, _ in R.pops(qr) if m.table[s][x] is None]

def show(w):
    return " ".join("#" if t == "#" else "%d^%s" % t for t in w)

if __name__ == "__main__":
    mt = sys.argv[1]; M = int(sys.argv[2]); c1 = int(sys.argv[3]); c0 = int(sys.argv[4])
    r = search(mt, M, c1, c0, verbose=len(sys.argv) > 5)
    if r is None: print("too big"); sys.exit()
    m, L, R, S = r
    h = halting(m, R, S)
    print("M=%d cap1=%d cap0=%d: S=%d L=%d R=%d halting=%d" % (M, c1, c0, len(S), len(L.states), len(R.states), len(h)))
    for (s, ql, qr, x) in h[:8]:
        print("  ", STATES[s], x, "| L:", show(L.states[ql]), "| R:", show(R.states[qr]))
