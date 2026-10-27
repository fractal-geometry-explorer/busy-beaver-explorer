"""Closure of run-start states. A right-end run ends at a meeting that is not the countdown's next one, and that
meeting starts the next run, so every run-start state is the round-start state of some run's final round.
Starting from the clean tape (G, end marker) and from the loop state G W W W, explore each state exhaustively with all
positions free (end marker tied to the end), collect the round-start shapes of every final round, and repeat with the
new shapes until no new shape appears. Reports, per shape: longest run before reaching G W W W, longest run that ends
without it, capped paths, halts, and geometry-dependent comparisons."""
import sys, copy, itertools, collections, time
from fractions import Fraction as F
from tree4 import TModel, Coset, Branch, Pos, pred_form

LOOP = ['GWWW', 'GBW', 'GMB', 'GMWW', 'GMB', 'GMWW', 'GWWW', 'GBW']


def explore(shape, Wv, posv, par, cap, stop_gwww):
    free = [i for i, (t, p) in enumerate(zip(shape[1:], posv)) if not (t == 'M' and p == Wv - 2)]
    nv = len(free) + 1
    res = {'ncmp': 0, 'bad': 0, 'capped': 0, 'halt': 0, 'to': collections.Counter(), 'no': collections.Counter(), 'new': {}, 'paths': 0}

    def forced(f, g):
        d = [x - y for x, y in zip(f.f, g.f)][:nv]
        if all(x == 0 for x in d):
            return True
        beta = [sum(d[k:]) for k in range(nv)]
        return all(b >= 0 for b in beta) or all(b <= 0 for b in beta)

    def note(f, g):
        res['ncmp'] += 1
        if not forced(f, g):
            res['bad'] += 1

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
    Ef = [F(0)] * (nv + 1); Ef[nv - 1] = F(1); m.W = Pos(Ef, F(Wv))
    for i, (t, p) in enumerate(zip(shape[1:], posv)):
        if i in free:
            f = [F(0)] * (nv + 1); f[free.index(i)] = F(1); m.add(t, Pos(f, F(p)))
        else:
            m.add(t, m.W - 2)
    m.add('G', m.const(1)); m.run = []; m.hist = [shape]
    c = Coset(list(par), [[2 * (i == j) for j in range(nv)] for i in range(nv)])
    stack = [(m, c, [])]
    while stack:
        m0, c0, fo = stack.pop()
        mm = copy.deepcopy(m0); cc = c0.copy(); mm.setup_tree(cc); mm.forced = fo; ne0 = len(mm.endd)
        try:
            mm.do_round()
        except Branch:
            if c0.bits + len(fo) + 1 > cap:
                res['capped'] += 1; continue
            stack.append((m0, c0, fo + [0])); stack.append((m0, c0, fo + [2])); continue
        except AssertionError:
            continue
        if mm.halted:
            res['halt'] += 1; continue
        if mm.bad:
            continue
        mm.hist.append(mm.shape()); broken = False
        for (rr, d) in mm.endd[ne0:]:
            if mm.run and pred_form(*mm.run[-1]).f != d.f:
                if len(mm.hist) == 2:
                    mm.run = []
                else:
                    broken = True; break
            mm.run.append((d, cc.decided(d.f)))
        if broken:
            res['paths'] += 1; res['no'][len(mm.run)] += 1
            mk = m0.marks(); sh = m0.shape()
            if sh not in res['new']:
                res['new'][sh] = (int(m0.W.v), [int(p.v) for t, p in mk[1:]])
            continue
        if stop_gwww and mm.run and mm.hist[-1] == 'GWWW' and len(mm.hist) > 1:
            res['paths'] += 1; res['to'][len(mm.run)] += 1; continue
        if not stop_gwww and len(mm.hist) == 9 and not broken and any(all(mm.hist[k] == LOOP[(ph + k) % 8] for k in range(9)) for ph in (0, 6)):
            continue   # a complete pass: back to a loop state, covered by this same search
        mk = mm.marks(); fin = len(mk) == 2 and mk[1][0] == 'M' and mk[1][1].v == mm.W.v - 2
        if fin or (stop_gwww and len(mm.hist) == 2 and not mm.run) or len(mm.hist) > 300:
            res['paths'] += 1; res['no'][len(mm.run)] += 1; continue
        stack.append((mm, cc, []))
    return res


if __name__ == '__main__':
    cap = int(sys.argv[1])
    SC = 2 ** 200
    queue = collections.OrderedDict()
    queue['GM'] = (SC, [SC - 2])                       # clean tape: gap at 1, end marker
    queue['GWWW'] = (10395969088 * (SC >> 34), [1559396385 * (SC >> 34), 6743276446 * (SC >> 34), 10381864607 * (SC >> 34)])
    done = set(); t0 = time.time()
    while queue:
        shape, (Wv, posv) = queue.popitem(last=False)
        if shape in done:
            continue
        done.add(shape)
        nfree = len([1 for t, p in zip(shape[1:], posv) if not (t == 'M' and p == Wv - 2)]) + 1
        agg_to = collections.Counter(); agg_no = collections.Counter(); capped = halts = badc = ncmp = valid = 0; newsh = {}
        for par in itertools.product((0, 1), repeat=nfree):
            r = explore(shape, Wv, posv, par, cap, stop_gwww=(shape != 'GWWW'))
            if r['paths'] == 0:
                continue
            valid += 1; agg_to.update(r['to']); agg_no.update(r['no']); capped += r['capped']; halts += r['halt']
            badc += r['bad']; ncmp += r['ncmp']
            for k, v in r['new'].items():
                newsh.setdefault(k, v)
        fresh = [k for k in newsh if k not in done and k not in queue]
        for k in fresh:
            queue[k] = newsh[k]
        print(f"[{time.time() - t0:7.0f}s] {shape:10s} {valid:3d} parity classes | to GWWW within {max(agg_to) if agg_to else '-'} | "
              f"ends within {max(agg_no) if agg_no else '-'} | capped {capped} | halts {halts} | geometry-dependent {badc}/{ncmp} | "
              f"next-run shapes {sorted(newsh)} | new {fresh}", flush=True)
    print("closed: no new run-start shapes.", sorted(done))
