"""From generic G M B states, find a branch that runs the loop-with-an-extra-wall for a full pass, turn its coset into
a concrete integer state near the virtual geometry, and report the concrete run."""
import itertools, copy, sys
from fractions import Fraction as F
from tree4 import TModel, Coset, Branch, Pos, pred_form
from conc import Model, fmt
SC = 2 ** 60
tok = [l.split() for l in open('prerun_examples.txt') if l.startswith('GMB ')][0]
Wv = int(tok[1]) * SC; posv = [int(x) * SC for x in tok[2:]]
EXTSEQ = ['GWWWW', 'GBWW', 'GMBW', 'GMWWW', 'GMBW', 'GMWWW', 'GWWWW', 'GBWW']
def has_ext(h):
    s = ' '.join(h); return ' '.join(EXTSEQ) in s
for par in itertools.product((0, 1), repeat=3):
    m = TModel(3)
    m.W = Pos([F(0), F(0), F(1), F(0)], F(Wv)); m.add('M', Pos([F(1), F(0), F(0), F(0)], F(posv[0]))); m.add('B', Pos([F(0), F(1), F(0), F(0)], F(posv[1])))
    m.add('G', m.const(1)); m.run = []; m.hist = ['GMB']
    c = Coset(list(par), [[2 * (i == j) for j in range(3)] for i in range(3)])
    stack = [(m, c, [])]; done = False
    while stack and not done:
        m0, c0, fo = stack.pop()
        mm = copy.deepcopy(m0); cc = c0.copy(); mm.setup_tree(cc); mm.forced = fo
        try: mm.do_round()
        except Branch:
            if c0.bits + len(fo) + 1 > 30: continue
            stack.append((m0, c0, fo + [0])); stack.append((m0, c0, fo + [2])); continue
        except AssertionError: continue
        if mm.halted or mm.bad: continue
        mm.hist.append(mm.shape())
        if has_ext(mm.hist):
            # concrete point: x = x0 + B y close to the virtual values
            virt = [posv[0], posv[1], Wv]
            K = 2 ** (cc.bits + 8)
            # simple: x = x0 + 2^(bits+...)*k is not right for general B; solve y = B^-1 (virt - x0) rounded
            import fractions
            Bm = cc.B; x0 = cc.x0
            # invert 3x3
            def det3(M): return (M[0][0]*(M[1][1]*M[2][2]-M[1][2]*M[2][1]) - M[0][1]*(M[1][0]*M[2][2]-M[1][2]*M[2][0]) + M[0][2]*(M[1][0]*M[2][1]-M[1][1]*M[2][0]))
            D = det3(Bm)
            def cof(i, j):
                rows = [r for k, r in enumerate(Bm) if k != i]; sub = [[x for l, x in enumerate(r) if l != j] for r in rows]
                return (-1) ** (i + j) * (sub[0][0] * sub[1][1] - sub[0][1] * sub[1][0])
            inv = [[F(cof(j, i), D) for j in range(3)] for i in range(3)]
            y = [round(sum(inv[i][j] * (virt[j] - x0[j]) for j in range(3))) for i in range(3)]
            x = [x0[i] + sum(Bm[i][j] * y[j] for j in range(3)) for i in range(3)]
            print("parities", par, "bits", cc.bits, "path:", ' '.join(mm.hist))
            print("concrete M, B, E =", x)
            mc = Model(1); mc.W = mc.const(x[2]); mc.add('M', mc.const(x[0])); mc.add('B', mc.const(x[1])); mc.add('G', mc.const(1))
            hs = ['GMB']
            for r in range(40):
                mc.do_round(); hs.append(mc.shape())
                if mc.bad or mc.halted: break
            print("concrete run:", ' '.join(hs))
            done = True; break
        mk = mm.marks(); fin = len(mk) == 2 and mk[1][0] == 'M' and mk[1][1].v == mm.W.v - 2
        if fin or len(mm.hist) > 30: continue
        stack.append((mm, cc, []))
    if done: break
