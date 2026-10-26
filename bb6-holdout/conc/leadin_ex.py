"""Exhaustive search from a run-start state of a given shape, all positions free (the end marker tied to the end):
follow the right-end run that starts in the first round until it reaches a G W W W state (from there the loop-exit
result applies) or ends. No cut is used unless a path exceeds the safety cap. Also checks that every order
comparison is forced on the cone x1 < x2 < ... < E."""
import sys, copy, itertools, collections
from fractions import Fraction as F
from tree4 import TModel, Coset, Branch, Pos, pred_form


class Stats:
    pass


def run_shape(shape, Wv, posv, par, cap, SC=2 ** 200, stop_at=('GWWW',)):
    free = [i for i, (t, p) in enumerate(zip(shape[1:], posv)) if not (t == 'M' and p == Wv - 2)]
    nv = len(free) + 1
    st = Stats(); st.ncmp = 0; st.badcmp = 0; st.examples = []

    def forced(f, g):
        d = [x - y for x, y in zip(f.f, g.f)][:nv]
        if all(x == 0 for x in d):
            return True
        beta = [sum(d[k:]) for k in range(nv)]
        return all(b >= 0 for b in beta) or all(b <= 0 for b in beta)

    def note(f, g):
        st.ncmp += 1
        if not forced(f, g):
            st.badcmp += 1

    class GM(TModel):
        def first_right(self, x):
            b = -1
            for i in range(len(self.T)):
                if self.A[i]:
                    note(self.P[i], x)
                    if self.P[i].v > x.v:
                        if b >= 0:
                            note(self.P[i], self.P[b])
                        if b < 0 or self.P[i].v < self.P[b].v:
                            b = i
            return b

        def last_mark(self):
            b = -1
            for i in range(len(self.T)):
                if self.A[i]:
                    if b >= 0:
                        note(self.P[i], self.P[b])
                    if b < 0 or self.P[i].v > self.P[b].v:
                        b = i
            return b

        def packet_back(self, x):
            b = -1
            for i in range(len(self.T)):
                if self.A[i] and self.T[i] != 'M':
                    note(self.P[i], x)
                    if self.P[i].v < x.v:
                        if b >= 0:
                            note(self.P[i], self.P[b])
                        if b < 0 or self.P[i].v > self.P[b].v:
                            b = i
            if b < 0:
                return -1
            if self.T[b] == 'B':
                self.halted = True; return -1
            if self.T[b] == 'G':
                self.P[b] = self.P[b] + 2; return b
            q = self.P[b]; self.T[b] = 'M'; self.P[b] = q - 1; return self.add('G', q + 1)

    GM.do_round = TModel.do_round
    m = GM(nv)
    Ef = [F(0)] * (nv + 1); Ef[nv - 1] = F(1); m.W = Pos(Ef, F(Wv) * SC)
    for i, (t, p) in enumerate(zip(shape[1:], posv)):
        if i in free:
            f = [F(0)] * (nv + 1); f[free.index(i)] = F(1); m.add(t, Pos(f, F(p) * SC))
        else:
            m.add(t, m.W - 2)
    m.add('G', m.const(1)); m.run = []; m.hist = []
    c = Coset(list(par), [[2 * (i == j) for j in range(nv)] for i in range(nv)])
    stack = [(m, c, [])]
    st.capped = 0; st.toloop = collections.Counter(); st.noloop = collections.Counter(); st.err = 0; st.halt = 0
    while stack:
        m0, c0, fo = stack.pop()
        mm = copy.deepcopy(m0); cc = c0.copy(); mm.setup_tree(cc); mm.forced = fo; ne0 = len(mm.endd)
        try:
            mm.do_round()
        except Branch:
            if c0.bits + len(fo) + 1 > cap:
                st.capped += 1; continue
            stack.append((m0, c0, fo + [0])); stack.append((m0, c0, fo + [2])); continue
        except AssertionError:
            st.err += 1; continue
        if mm.halted:
            st.halt += 1; continue
        if mm.bad:
            st.err += 1; continue
        mm.hist.append(mm.shape()); broken = False
        for (rr, d) in mm.endd[ne0:]:
            if mm.run and pred_form(*mm.run[-1]).f != d.f:
                if len(mm.hist) == 1:
                    mm.run = []
                else:
                    broken = True; break
            mm.run.append((d, cc.decided(d.f)))
        if not broken and mm.run and mm.hist[-1] in stop_at:
            st.toloop[len(mm.run)] += 1; continue
        mk = mm.marks(); fin = len(mk) == 2 and mk[1][0] == 'M' and mk[1][1].v == mm.W.v - 2
        if broken or fin or not mm.run or len(mm.hist) > 300:
            st.noloop[len(mm.run)] += 1
            if len(mm.run) >= 6 and len(st.examples) < 3:
                st.examples.append(' '.join(mm.hist))
            continue
        stack.append((mm, cc, []))
    return st


if __name__ == '__main__':
    cap = int(sys.argv[1]); which = sys.argv[2:]
    for line in open('prerun_examples.txt'):
        tok = line.split(); shape = tok[0]
        if which and shape not in which:
            continue
        Wv = int(tok[1]); posv = [int(x) for x in tok[2:]]
        nfree = len([1 for t, p in zip(shape[1:], posv) if not (t == 'M' and p == Wv - 2)]) + 1
        agg_to = collections.Counter(); agg_no = collections.Counter(); capped = 0; badc = 0; ncmp = 0; valid = 0; halts = 0; ex = []
        for par in itertools.product((0, 1), repeat=nfree):
            st = run_shape(shape, Wv, posv, par, cap)
            if not st.toloop and not st.noloop:
                continue
            valid += 1; agg_to.update(st.toloop); agg_no.update(st.noloop); capped += st.capped
            badc += st.badcmp; ncmp += st.ncmp; halts += st.halt; ex += st.examples
        print(f"{shape:9s} {valid:2d} parity classes | reaches GWWW after at most {max(agg_to) if agg_to else '-'} run meetings | "
              f"runs that end first: at most {max(agg_no) if agg_no else '-'} | paths capped {capped} | halts {halts} | "
              f"geometry-dependent comparisons {badc} of {ncmp}", flush=True)
        for e in ex[:2]:
            print("     long run without the loop:", e)
