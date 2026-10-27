"""Exact branching from a run-start state of a given shape with every position free (only parities fixed): the run
that starts with the next end meeting; count its meetings before it reaches the loop (a stretch of 4 loop rounds),
or all of them if it never does.  Prints the largest counts over all paths above the density cut."""
import sys, copy, collections, itertools
from fractions import Fraction as F
from tree4 import TModel, Coset, Branch, Pos, pred_form
LOOP = ['GWWW', 'GBW', 'GMB', 'GMWW', 'GMB', 'GMWW', 'GWWW', 'GBW']
def in_loop(hist):
    # does hist end with 4 consecutive loop rounds?
    if len(hist) < 4: return False
    tail = hist[-4:]
    return any(all(tail[k] == LOOP[(ph + k) % 8] for k in range(4)) for ph in range(8))
def explore(shape, Wv, posv, par, cut, SC):
    # marks other than an end marker (M at W - 2) get their own variable; the end marker is tied to the end
    free = [i for i, (t, p) in enumerate(zip(shape[1:], posv)) if not (t == 'M' and p == Wv - 2)]
    nv = len(free) + 1
    m = TModel(nv)
    Ef = [F(0)] * (nv + 1); Ef[nv - 1] = F(1); m.W = Pos(Ef, F(Wv) * SC)
    for i, (t, p) in enumerate(zip(shape[1:], posv)):
        if i in free:
            f = [F(0)] * (nv + 1); f[free.index(i)] = F(1); m.add(t, Pos(f, F(p) * SC))
        else:
            m.add(t, m.W - 2)
    m.add('G', m.const(1))
    m.run = []; m.hist = []; m.pre = None
    c = Coset(list(par), [[2 * (i == j) for j in range(nv)] for i in range(nv)])
    stack = [(m, c, [])]; best_pre = 0; best_noloop = 0; npaths = 0; nerr = 0; mass_loop = F(0)
    while stack:
        m0, c0, forced = stack.pop()
        mm = copy.deepcopy(m0); cc = c0.copy(); mm.setup_tree(cc); mm.forced = forced; ne0 = len(mm.endd)
        try: mm.do_round()
        except Branch:
            if c0.bits + len(forced) + 1 > cut: continue
            stack.append((m0, c0, forced + [0])); stack.append((m0, c0, forced + [2])); continue
        except AssertionError: nerr += 1; continue
        if mm.halted or mm.bad: nerr += 1; continue
        mm.hist.append(mm.shape())
        broken = False
        for (rr, d) in mm.endd[ne0:]:
            if mm.run and pred_form(*mm.run[-1]).f != d.f: broken = True; break
            mm.run.append((d, cc.decided(d.f)))
        mk = mm.marks(); done = len(mk) == 2 and mk[1][0] == 'M' and mk[1][1].v == mm.W.v - 2
        if mm.run and in_loop(mm.hist):
            # meetings before the 4-round loop stretch began: count meetings in rounds before len(hist)-4
            npaths += 1; mass_loop += F(1, 2 ** cc.bits)
            pre = len(mm.run)   # upper bound (includes meetings inside the 4 loop rounds)
            best_pre = max(best_pre, pre); continue
        if broken or done or len(mm.hist) > 200:
            npaths += 1; best_noloop = max(best_noloop, len(mm.run)); continue
        stack.append((mm, cc, []))
    return npaths, nerr, best_pre, best_noloop, mass_loop
if __name__ == '__main__':
    cut = int(sys.argv[1]); which = sys.argv[2:] 
    for line in open('prerun_examples.txt'):
        tok = line.split(); shape = tok[0]
        if which and shape not in which: continue
        Wv = int(tok[1]); posv = [int(x) for x in tok[2:]]
        nv = len([1 for t, p in zip(shape[1:], posv) if not (t == 'M' and p == Wv - 2)]) + 1
        tot = collections.Counter(); bp = 0; bn = 0; ml = F(0); valid = 0
        base = [p % 2 for p in posv] + [Wv % 2]
        for par in itertools.product((0, 1), repeat=nv):
            npaths, nerr, best_pre, best_noloop, mass_loop = explore(shape, Wv, posv, par, cut, 2 ** 150)
            if npaths == 0: continue
            valid += 1; bp = max(bp, best_pre); bn = max(bn, best_noloop); ml += mass_loop
        print(f"{shape:9s}: {valid} parity classes; most run meetings up to reaching the loop {bp}; longest run that never reaches it {bn}; P(reach loop) summed {float(ml):.3g}", flush=True)
