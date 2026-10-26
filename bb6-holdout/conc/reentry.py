"""Exact branching from block states (as tree_block.py), keeping each path's shape history: does any run leave the
loop and come back to it without the run breaking?"""
import sys, copy
from fractions import Fraction as F
from tree4 import TModel, Coset, Branch, Pos, pred_form
LOOP = ['GWWW', 'GBW', 'GMB', 'GMWW', 'GMB', 'GMWW', 'GWWW', 'GBW']
def stretches(sh):
    out = []; i = 0
    while i < len(sh):
        best = 0
        for ph in range(8):
            k = 0
            while i + k < len(sh) and sh[i + k] == LOOP[(ph + k) % 8]: k += 1
            best = max(best, k)
        if best >= 4: out.append((i, best)); i += best
        else: i += 1
    return out
cut = int(sys.argv[1]); geo = sys.argv[2] if len(sys.argv) > 2 else 'a'
SC = 2 ** 200
E = SC
if geo == 'a': r = (SC * 3 // 10) & ~1; D = (SC // 200) | 1
else: r = (SC * 6 // 10) & ~1; D = (SC // 9) | 1
R = E - D
m = TModel(3); m.W = Pos([F(0), F(0), F(1), F(0)], F(E))
m.add('G', m.const(1)); m.add('B', Pos([F(1), F(0), F(0), F(0)], F(r))); m.add('W', Pos([F(0), F(1), F(0), F(0)], F(R)))
m.run = []; m.hist = []; m.runstart = 0
c = Coset([0, 1, 0], [[2, 0, 0], [0, 2, 0], [0, 0, 2]])
stack = [(m, c, [])]; npaths = 0; multi = 0; longest = 0
import collections; byL = collections.Counter()
while stack:
    m0, c0, forced = stack.pop()
    mm = copy.deepcopy(m0); cc = c0.copy(); mm.setup_tree(cc); mm.forced = forced; ne0 = len(mm.endd)
    try: mm.do_round()
    except Branch:
        if c0.bits + len(forced) + 1 > cut: continue
        stack.append((m0, c0, forced + [0])); stack.append((m0, c0, forced + [2])); continue
    if mm.halted or mm.bad: continue
    mm.hist.append(mm.shape())
    broken = False
    for (rr, d) in mm.endd[ne0:]:
        if mm.run and pred_form(*mm.run[-1]).f != d.f: broken = True; break
        if not mm.run: mm.runstart = len(mm.hist) - 1
        mm.run.append((d, cc.decided(d.f)))
    mk = mm.marks(); done = len(mk) == 2 and mk[1][0] == 'M' and mk[1][1].v == mm.W.v - 2
    if broken or done:
        npaths += 1; L = len(mm.run); byL[L] += 1
        st = stretches(mm.hist[mm.runstart:])
        if len(st) >= 2:
            multi += 1
            if multi <= 5: print("re-entry: run", L, st, ' '.join(mm.hist[mm.runstart:]))
        longest = max(longest, L)
        continue
    stack.append((mm, cc, []))
print(f"paths {npaths}, longest run {longest}, runs with two or more loop stretches: {multi}")
