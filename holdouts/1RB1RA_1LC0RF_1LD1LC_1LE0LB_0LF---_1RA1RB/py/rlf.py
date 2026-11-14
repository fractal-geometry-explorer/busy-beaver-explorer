"""Side automaton = window of M runs + flags summarising the dropped (far) part."""
import sys
from rlctl import Side, Machine, STATES
def par(c): return (c % 2 == 0) if isinstance(c, int) else c == 'e'
class FSide(Side):
    # state: (flags, window); flags = (stage, Fpar, Eu, Ep, Z)
    def __init__(self, M, cap1, cap0, feats="FUPZ"):
        self.M, self.cap = M, {1: cap1, 0: cap0}
        self.feats = feats
        z = ((0, 0, 0, 0, 0), ("#",))
        self.states = [z]; self.index = {z: 0}; self.edges = set(); self.acc = [0]; self._pops = {}
    def nxt(self, st, x):
        fl, w = st
        if w == ("#",) and x == 0: return st
        if w[-1] != "#" and w[-1][0] == x:
            return (fl, w[:-1] + ((x, self.inc(x, w[-1][1])),))
        n = w + ((x, 1),)
        if len(n) > self.M:
            stage, F, Eu, Ep, Z = fl
            t = n[0]; n = n[1:]
            if t == "#": stage = 1
            elif t[0] == 1:
                if stage == 1:
                    stage = 2
                    if "F" in self.feats: F = 2 if par(t[1]) else 1
                elif par(t[1]):
                    prot = n[0] == (0, 1) and n[1] == (1, 1)
                    if prot:
                        if "P" in self.feats: Ep = 1
                    else:
                        if "U" in self.feats: Eu = 1
            else:
                if t[1] != 1 and "Z" in self.feats: Z = 1
            fl = (stage, F, Eu, Ep, Z)
        return (fl, n)
    def push(self, q, x):
        n = self.nxt(self.states[q], x)
        new = n not in self.index
        if new:
            self.index[n] = len(self.states); self.states.append(n)
        j = self.index[n]
        e = (j, x, q)
        if e not in self.edges:
            self.edges.add(e); self._pops.setdefault(j, []).append((x, q)); new = True
        return j, new
    def peek(self, q, x):
        return self.index.get(self.nxt(self.states[q], x))
def show(st):
    fl, w = st
    return "[%d%d%d%d%d] " % fl + " ".join("#" if t == "#" else "%d^%s" % t for t in w)
def observe(mt, L, R, steps):
    m = Machine.parse(mt)
    N = 1 << 21
    tape = bytearray(N); Ls = [0] * N; Rs = [0] * N
    p = N // 2; s = 0
    S = {(0, 0, 0)}
    for step in range(steps):
        t = m.table[s][tape[p]]
        w, d, s2 = t
        tape[p] = w
        if d == 1:
            Ls[p] = L.push(Ls[p - 1], w)[0]
            p += 1
        else:
            Rs[p] = R.push(Rs[p + 1], w)[0]
            Rs[p - 1] = R.push(Rs[p], tape[p - 1])[0]
            p -= 1
        S.add((s2, Ls[p - 1], Rs[p]))
        s = s2
    return m, S
def violations(m, L, R, S):
    out = []
    for (s, ql, qr) in S:
        for x, qr2 in R.pops(qr):
            t = m.table[s][x]
            if t is None: out.append(("HALT", s, ql, qr, x, qr2)); continue
            w, d, s2 = t
            if d == 1:
                nl = L.peek(ql, w)
                if nl is None or (s2, nl, qr2) not in S: out.append(("R", s, ql, qr, x, qr2))
            else:
                n1 = R.peek(qr2, w)
                for y, ql2 in L.pops(ql):
                    n0 = None if n1 is None else R.peek(n1, y)
                    if n0 is None or (s2, ql2, n0) not in S: out.append(("L", s, ql, qr, x, qr2, y, ql2))
    return out
def close(m, L, R, S, limit=300000):
    S = set(S)
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
        if len(S) > limit: return None
        if not changed: return S
def pr(L, R, x):
    kind, s, ql, qr = x[:4]
    extra = ""
    if kind == "L": extra = " popL y=%d rest: %s" % (x[6], show(L.states[x[7]]))
    print(kind, STATES[s], "| L:", show(L.states[ql]), "| R:", show(R.states[qr]), "| head", x[4], "rest:", show(R.states[x[5]]), extra)
if __name__ == "__main__":
    mt = sys.argv[1]; M = int(sys.argv[2]); c1 = int(sys.argv[3]); c0 = int(sys.argv[4]); steps = int(float(sys.argv[5]))
    feats = sys.argv[7] if len(sys.argv) > 7 else "FUPZ"
    L = FSide(M, c1, c0, feats); R = FSide(M, c1, c0, feats)
    m, S = observe(mt, L, R, steps)
    v = violations(m, L, R, S)
    import collections
    print("S=%d L=%d R=%d violations=%d" % (len(S), len(L.states), len(R.states), len(v)), collections.Counter(x[0] for x in v))
    print("L flags:", collections.Counter(st[0] for st in L.states)); print("R flags:", collections.Counter(st[0] for st in R.states))
    for x in v[:int(sys.argv[6]) if len(sys.argv) > 6 else 10]: pr(L, R, x)
