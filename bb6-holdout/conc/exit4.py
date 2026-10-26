"""Exact branching from a generic loop pass-start state (G, W a, W b, W c, end E; a, b, c, E free apart from parity):
follow the right-end run through any number of passes and out of the loop. Reports how many meetings the run makes
after leaving the loop, and whether it ever comes back."""
import sys, copy, collections
from fractions import Fraction as F
from tree4 import TModel, Coset, Branch, Pos, pred_form
from cyccost import vals
LOOP = ['GWWW', 'GBW', 'GMB', 'GMWW', 'GMB', 'GMWW', 'GWWW', 'GBW']
cut = int(sys.argv[1])
SC = 2 ** 200
big = [F(v) * SC for v in vals]
m = TModel(4)
for i in range(3): m.add('W', Pos([F(int(i == j)) for j in range(4)] + [F(0)], big[i]))
m.W = Pos([F(0), F(0), F(0), F(1), F(0)], big[3]); m.add('G', m.const(1))
m.run = []; m.hist = ['GWWW']; m.runmeet = []   # rounds (index into hist) of run meetings
c = Coset([v % 2 for v in vals], [[2 * (i == j) for j in range(4)] for i in range(4)])
stack = [(m, c, [])]; res = collections.Counter(); mass = collections.defaultdict(F); reentry = 0; npaths = 0
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
        mm.run.append((d, cc.decided(d.f))); mm.runmeet.append(len(mm.hist) - 1)
    mk = mm.marks(); done = len(mk) == 2 and mk[1][0] == 'M' and mk[1][1].v == mm.W.v - 2
    if broken or done or len(mm.hist) > 300:
        npaths += 1
        # loop stretch from the start (phase 0)
        k = 0
        while k < len(mm.hist) and mm.hist[k] == LOOP[k % 8]: k += 1
        inloop = sum(1 for r in mm.runmeet if r < k); after = len(mm.runmeet) - inloop
        # re-entry: a later stretch of >= 8 loop rounds
        later = False
        for i in range(k, len(mm.hist)):
            for ph in range(8):
                j = 0
                while i + j < len(mm.hist) and mm.hist[i + j] == LOOP[(ph + j) % 8]: j += 1
                if j >= 8: later = True
        if later:
            reentry += 1
            if reentry <= 3: print("re-entry:", ' '.join(mm.hist))
        passes = k // 8
        res[(passes, after)] += 1; mass[(passes, after)] += F(1, 2 ** cc.bits)
        continue
    stack.append((mm, cc, []))
print(f"paths {npaths}, re-entries {reentry}")
print("(complete passes, run meetings after leaving the loop): probability")
for kk in sorted(mass): print(" ", kk, f"{float(mass[kk]):.4g}")
