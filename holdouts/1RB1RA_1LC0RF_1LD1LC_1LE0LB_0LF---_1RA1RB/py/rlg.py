"""Side automaton: window of M items (runs, or groups (unit)^count of two exact runs) + flags of the dropped part."""
import sys
from rlctl import Machine, STATES
import rlf
def par(c): return (c % 2 == 0) if isinstance(c, int) else c[1] % 2 == 0
class GSide(rlf.FSide):
    def __init__(self, M, cap1, cap0, capg, feats="FUPZ", mod1=4, modg=2):
        rlf.FSide.__init__(self, M, cap1, cap0, feats); self.capg = capg; self.mod = {1: mod1, 0: 2, 'g': modg}
        self.cap['g'] = capg
    def inc(self, b, c):
        if isinstance(c, int):
            if c < self.cap[b]: return c + 1
            return ('m', (c + 1) % self.mod[b])
        return ('m', (c[1] + 1) % self.mod[b])
    def incg(self, c): return self.inc('g', c)
    def nxt(self, st, x):
        fl, w = st
        if w == ("#",) and x == 0: return st
        last = w[-1]
        if last != "#" and last[0] == x:
            return (fl, w[:-1] + ((x, self.inc(x, last[1])),))
        n = list(w)
        # the run w[-1] is now frozen: try to merge (w[-2], w[-1])
        if len(n) >= 2 and n[-1] != "#" and n[-2] != "#" and n[-1][0] in (0, 1) and n[-2][0] in (0, 1) \
                and isinstance(n[-1][1], int) and isinstance(n[-2][1], int):
            unit = (n[-2], n[-1])
            if len(n) >= 3 and n[-3] != "#" and n[-3][0] == 'g' and n[-3][1] == unit:
                n[-3:] = [('g', unit, self.incg(n[-3][2]))]
            elif len(n) >= 4 and (n[-4], n[-3]) == unit:
                n[-4:] = [('g', unit, 2)]
        n.append((x, 1))
        n = tuple(n)
        while len(n) > self.M:
            stage, F, Eu, Ep, Z = fl
            t = n[0]; n = n[1:]
            if t == "#": stage = 1
            else:
                runs = [t] if t[0] != 'g' else list(t[1])
                for r in runs:
                    if r[0] == 1:
                        if stage == 1:
                            stage = 2
                            if "F" in self.feats: F = 2 if par(r[1]) else 1
                        elif par(r[1]):
                            prot = t[0] != 'g' and (n[0] == ('g', ((0, 1), (1, 1)), n[0][2] if n[0][0] == 'g' else None) or (n[0] == (0, 1) and n[1] == (1, 1)))
                            if prot:
                                if "P" in self.feats: Ep = 1
                            elif "U" in self.feats: Eu = 1
                    elif r[1] != 1 and "Z" in self.feats: Z = 1
            fl = (stage, F, Eu, Ep, Z)
        return (fl, n)
def sc(c): return str(c) if isinstance(c, int) else "m%d" % c[1]
def showt(t):
    if t == "#": return "#"
    if t[0] == 'g': return "(%s)^%s" % (" ".join("%d^%s" % (r[0], sc(r[1])) for r in t[1]), sc(t[2]))
    return "%d^%s" % (t[0], sc(t[1]))
def show(st):
    fl, w = st
    return "[%d%d%d%d%d] " % fl + " ".join(showt(t) for t in w)
rlf.show = show
if __name__ == "__main__":
    import collections
    mt = sys.argv[1]; M = int(sys.argv[2]); c1 = int(sys.argv[3]); c0 = int(sys.argv[4]); cg = int(sys.argv[5]); steps = int(float(sys.argv[6]))
    feats = sys.argv[7]; lim = int(sys.argv[8]); m1 = int(sys.argv[9]); mg = int(sys.argv[10])
    L = GSide(M, c1, c0, cg, feats, m1, mg); R = GSide(M, c1, c0, cg, feats, m1, mg)
    m, S = rlf.observe(mt, L, R, steps)
    v = rlf.violations(m, L, R, S)
    print("observed S=%d L=%d R=%d violations=%d" % (len(S), len(L.states), len(R.states), len(v)), collections.Counter(x[0] for x in v), flush=True)
    if lim < 0:
        for x in v[:-lim]: rlf.pr(L, R, x)
        sys.exit()
    S2 = rlf.close(m, L, R, S, limit=lim)
    if S2 is None: print("blow-up"); sys.exit()
    h = [(s, ql, qr, x) for (s, ql, qr) in S2 for x, _ in R.pops(qr) if m.table[s][x] is None]
    print("closed S=%d L=%d R=%d halting=%d" % (len(S2), len(L.states), len(R.states), len(h)))
