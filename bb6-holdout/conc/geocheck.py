"""Re-run the exhaustive one-pass exit search and record every order comparison the model makes. A comparison between
affine forms in (a, b, c, E) is forced if the difference has one sign on the whole cone 0 < a < b < c < E (for large
distances), i.e. if the coefficients of t1..t4 (a = t1, b = t1 + t2, ...) are all >= 0 or all <= 0, or if the
difference is constant. Reports any comparison that depends on the geometry."""
import sys, copy
from fractions import Fraction as F
import tree4
from tree4 import TModel, Coset, Branch, Pos, pred_form
bad_cmp = []; ncmp = [0]
def forced(f, g):
    d = [x - y for x, y in zip(f.f, g.f)]
    al = d[:4]
    if all(x == 0 for x in al): return True
    beta = [sum(al[k:]) for k in range(4)]
    return all(b >= 0 for b in beta) or all(b <= 0 for b in beta)
def note(f, g):
    ncmp[0] += 1
    if not forced(f, g): bad_cmp.append((f.f, g.f))
class GModel(TModel):
    def first_right(self, x):
        b = -1
        for i in range(len(self.T)):
            if self.A[i]:
                note(self.P[i], x)
                if self.P[i].v > x.v:
                    if b >= 0: note(self.P[i], self.P[b])
                    if b < 0 or self.P[i].v < self.P[b].v: b = i
        return b
    def last_mark(self):
        b = -1
        for i in range(len(self.T)):
            if self.A[i]:
                if b >= 0: note(self.P[i], self.P[b])
                if b < 0 or self.P[i].v > self.P[b].v: b = i
        return b
    def packet_back(self, x):
        b = -1
        for i in range(len(self.T)):
            if self.A[i] and self.T[i] != 'M':
                note(self.P[i], x)
                if self.P[i].v < x.v:
                    if b >= 0: note(self.P[i], self.P[b])
                    if b < 0 or self.P[i].v > self.P[b].v: b = i
        if b < 0: return -1
        if self.T[b] == 'B': self.halted = True; return -1
        if self.T[b] == 'G': self.P[b] = self.P[b] + 2; self.path.append('pg'); return b
        q = self.P[b]; self.T[b] = 'M'; self.P[b] = q - 1; self.path.append('pw'); return self.add('G', q + 1)
GModel.do_round = TModel.do_round
LOOP = ['GWWW', 'GBW', 'GMB', 'GMWW', 'GMB', 'GMWW', 'GWWW', 'GBW']
par = [int(x) for x in sys.argv[1]]
SC = 2 ** 200; big = [F(v) * SC for v in [1559396385, 6743276446, 10381864607, 10395969088]]
m = GModel(4)
for i in range(3): m.add('W', Pos([F(int(i == j)) for j in range(4)] + [F(0)], big[i]))
m.W = Pos([F(0), F(0), F(0), F(1), F(0)], big[3]); m.add('G', m.const(1)); m.run = []; m.hist = ['GWWW']
c = Coset(par, [[2 * (i == j) for j in range(4)] for i in range(4)])
def loop_ok(h): return any(all(h[k] == LOOP[(ph + k) % 8] for k in range(len(h))) for ph in (0, 6))
stack = [(m, c, [])]; ex = 0
while stack:
    m0, c0, forced_ = stack.pop()
    mm = copy.deepcopy(m0); cc = c0.copy(); mm.setup_tree(cc); mm.forced = forced_; ne0 = len(mm.endd)
    try: mm.do_round()
    except Branch:
        stack.append((m0, c0, forced_ + [0])); stack.append((m0, c0, forced_ + [2])); continue
    except AssertionError: continue
    if mm.halted or mm.bad: continue
    mm.hist.append(mm.shape()); broken = False
    for (rr, d) in mm.endd[ne0:]:
        if mm.run and pred_form(*mm.run[-1]).f != d.f: broken = True; break
        mm.run.append((d, cc.decided(d.f)))
    if len(mm.hist) == 9 and loop_ok(mm.hist) and not broken: continue
    mk = mm.marks(); fin = len(mk) == 2 and mk[1][0] == 'M' and mk[1][1].v == mm.W.v - 2
    if broken or fin or len(mm.hist) > 120: ex += 1; continue
    stack.append((mm, cc, []))
print(f"exits {ex}; comparisons made {ncmp[0]}; geometry-dependent comparisons {len(bad_cmp)}")
seen = set()
for f, g in bad_cmp:
    k = (tuple(f), tuple(g))
    if k in seen: continue
    seen.add(k); print("  ", [str(x) for x in f], "vs", [str(x) for x in g])
    if len(seen) > 8: break
