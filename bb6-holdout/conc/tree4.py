"""Exact 2-adic branching for runs of right-end meetings, starting from a block state with several free variables.
Every position is an affine form in the variables; geometry (which mark is nearest) comes from a scaled-up real
point; each d (mod 4) test is either fixed on the current coset or splits it into two halves (one bit).
Output: P(run reaches L meetings) for each L, summed exactly over all paths above a density cut."""
import sys, copy
from fractions import Fraction as F
from conc import Model, Pos, fmt

class Branch(Exception): pass

class Coset:
    def __init__(self, x0, B): self.x0 = list(x0); self.B = [row[:] for row in B]; self.bits = 0
    def copy(self):
        c = Coset(self.x0, self.B); c.bits = self.bits; return c
    def evalf(self, form):          # f(x0) and g = coefficients on y
        n = len(self.x0)
        f0 = form[n] + sum(form[i] * self.x0[i] for i in range(n))
        g = [sum(form[i] * self.B[i][k] for i in range(n)) for k in range(n)]
        return f0, g
    def impose(self, form, res):
        f0, g = self.evalf(form); n = len(self.x0)
        assert f0.denominator == 1 and all(x.denominator == 1 for x in g), "non-integral form on coset"
        f0 = int(f0); g = [int(x) for x in g]
        assert f0 % 2 == 0 and all(x % 2 == 0 for x in g), "odd distance on coset"
        h = [x // 2 for x in g]; t = ((res - f0) // 2) % 2
        odd = [k for k in range(n) if h[k] % 2]
        if not odd:
            return (f0 // 2) % 2 == res // 2
        i = odd[0]
        # y_i = t - sum_{k != i} h_k y_k + 2 z   (h_i odd)
        for r in range(n): self.x0[r] += t * self.B[r][i]
        for k in range(n):
            if k != i:
                for r in range(n): self.B[r][k] -= h[k] * self.B[r][i]
        for r in range(n): self.B[r][i] *= 2
        self.bits += 1
        return True
    def decided(self, form):
        f0, g = self.evalf(form)
        g = [int(x) for x in g]
        if all((x // 2) % 2 == 0 for x in g): return int(f0) % 4
        return None

class TModel(Model):
    """Model whose d tests consult the coset; undetermined tests take forced outcomes or raise Branch."""
    def setup_tree(self, coset): self.coset = coset; self.forced = []; self.fi = 0
    def test_outcome(self, d):
        dec = self.coset.decided(d.f)
        if dec is not None: return dec
        if self.fi < len(self.forced):
            res = self.forced[self.fi]; self.fi += 1
            self.coset.impose(d.f, res); return res
        raise Branch()

def pred_form(d, res):   # chain rule on forms
    return (d - 2).half() if res == 2 else d.half() + 4

def patch():
    # replace the test inside do_round by test_outcome; done by subclass override of do_round copy
    import inspect, textwrap
    src = inspect.getsource(Model.do_round)
    src = src.replace("""                if self.force is None:
                    if d.v < 0 or d.v % 2: self.bad = 3; return
                    res = d.v % 4
                else:
                    if d.v < 0 or not self.force: self.bad = 3; return
                    res = self.force.pop(0)""", """                if d.v < 0: self.bad = 3; return
                self.cur_last = (m == self.last_mark()); res = self.test_outcome(d)""")
    ns = {}
    exec(textwrap.dedent(src), {'F': F, 'Pos': Pos}, ns)
    TModel.do_round = ns['do_round']
patch()

def run_tree(start_model, coset, Lmax, cut_bits, max_rounds=400):
    reach = [F(0)] * (Lmax + 2)
    stack = [(start_model, coset, [], 0)]   # model at round start, coset at round start, forced outcomes, rounds done
    npaths = 0; lost = [F(0)]
    while stack:
        m0, c0, forced, rd = stack.pop()
        m = copy.deepcopy(m0); c = c0.copy(); m.setup_tree(c); m.forced = forced
        ne0 = len(m.endd)
        try:
            m.do_round()
        except Branch:
            if c0.bits + len(forced) + 1 > cut_bits:
                lost[0] += F(1, 2 ** (c0.bits + len(forced))); continue
            stack.append((m0, c0, forced + [0], rd)); stack.append((m0, c0, forced + [2], rd)); continue
        except AssertionError as e:
            print("assert:", e); continue
        if m.halted or m.bad: print("halted/bad", m.halted, m.bad); continue
        # chain bookkeeping: m.chain = list of (d form, res) for the current run
        broken = False
        newends = m.endd[ne0:]
        for d in [dd for (rr, dd) in newends]:
            if m.run:
                pd = pred_form(*m.run[-1])
                if pd.f != d.f: broken = True; break
            res = c.decided(d.f)
            m.run.append((d, res))
        L = len(m.run)
        mk = m.marks()
        done = len(mk) == 2 and mk[1][0] == 'M' and mk[1][1].v == m.W.v - 2
        if broken or done or rd + 1 >= max_rounds:
            Lf = L
            for l in range(1, min(Lf, Lmax + 1) + 1): reach[l] += F(1, 2 ** c.bits)
            npaths += 1
            continue
        stack.append((m, c, [], rd + 1))
    return reach, npaths, lost[0]
