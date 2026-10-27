"""From a generic loop pass-start state (G, W a, W b, W c, end E), explore every branch of ONE pass: a path that
completes the pass (back to a pass-start state after 8 rounds, in either loop phase) is set aside; every other path
is followed until its right-end run ends. Reports whether any path hit the bit cut (so the search is exhaustive if
none did), the most run meetings after the loop pattern breaks, and any return to the loop."""
import sys, copy, collections
from fractions import Fraction as F
from tree4 import TModel, Coset, Branch, Pos, pred_form
LOOP = ['GWWW', 'GBW', 'GMB', 'GMWW', 'GMB', 'GMWW', 'GWWW', 'GBW']
cut = int(sys.argv[1]); par = [int(x) for x in sys.argv[2]]; geo = int(sys.argv[3])
GEOS = [[1559396385, 6743276446, 10381864607, 10395969088], [1000, 5000, 9000, 10000], [3000, 4000, 9990, 10000], [100, 9000, 9500, 10000], [2000, 7600, 9999, 10000]]
SC = 2 ** 200; big = [F(v) * SC for v in GEOS[geo]]
m = TModel(4)
for i in range(3): m.add('W', Pos([F(int(i == j)) for j in range(4)] + [F(0)], big[i]))
m.W = Pos([F(0), F(0), F(0), F(1), F(0)], big[3]); m.add('G', m.const(1))
m.run = []; m.hist = ['GWWW']
c = Coset(par, [[2 * (i == j) for j in range(4)] for i in range(4)])
stack = [(m, c, [])]; hitcut = 0; done_pass = F(0); after = collections.Counter(); back = 0; npaths = 0; errs = 0
def loop_ok(hist):
    return any(all(hist[k] == LOOP[(ph + k) % 8] for k in range(len(hist))) for ph in (0, 6))
while stack:
    m0, c0, forced = stack.pop()
    mm = copy.deepcopy(m0); cc = c0.copy(); mm.setup_tree(cc); mm.forced = forced; ne0 = len(mm.endd)
    try: mm.do_round()
    except Branch:
        if c0.bits + len(forced) + 1 > cut: hitcut += 1; continue
        stack.append((m0, c0, forced + [0])); stack.append((m0, c0, forced + [2])); continue
    except AssertionError: errs += 1; continue
    if mm.halted or mm.bad: errs += 1; continue
    mm.hist.append(mm.shape())
    broken = False
    for (rr, d) in mm.endd[ne0:]:
        if mm.run and pred_form(*mm.run[-1]).f != d.f: broken = True; break
        mm.run.append((d, cc.decided(d.f)))
    if len(mm.hist) == 9 and loop_ok(mm.hist) and not broken:
        done_pass += F(1, 2 ** cc.bits); continue
    mk = mm.marks(); fin = len(mk) == 2 and mk[1][0] == 'M' and mk[1][1].v == mm.W.v - 2
    if broken or fin or len(mm.hist) > 120:
        npaths += 1
        # rounds following the loop pattern from the start
        k = 0
        for ph0 in (0, 6):
            kk = 0
            while kk < len(mm.hist) and mm.hist[kk] == LOOP[(ph0 + kk) % 8]: kk += 1
            k = max(k, kk)
        meet_rounds = []
        # count run meetings after round k: approximate via the number of run meetings minus those in loop rounds
        after[len(mm.run)] += 1
        found = False
        for i in range(k, len(mm.hist)):
            for ph in range(8):
                j = 0
                while i + j < len(mm.hist) and mm.hist[i + j] == LOOP[(ph + j) % 8]: j += 1
                if j >= 4: found = True
        if found:
            back += 1
            if back <= 3: print("returns:", ' '.join(mm.hist))
        if len(mm.hist) > 120: print("long path:", ' '.join(mm.hist[:40]))
        continue
    stack.append((mm, cc, []))
print(f"parities {sys.argv[2]} geometry {geo}: exits {npaths}, paths cut {hitcut}, P(pass completes) {float(done_pass):.6f}, "
      f"returns to 4+ loop rounds after leaving {back}; run lengths of exits (meetings from the pass start): {dict(sorted(after.items()))}")
