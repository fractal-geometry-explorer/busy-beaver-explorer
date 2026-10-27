"""The first segment of every clean tape, symbolically: one variable N = 2n + 6 (the clean tape's width), every branch
followed with exact 2-adic cosets until the segment ends (a GMM state or a clean tape) or a phase-0 plain entry appears.
usage: firstseg_sym.py cut"""
import sys
from fractions import Fraction as F
import endsym as ES
ES.NV = 1; ES.NOBREAK = True
from endsym import Pos, cpos, Coset, Ctx, check_tape, do_round, Stop, Branch, Inconsistent
cut = int(sys.argv[1])
N = Pos([F(1), F(0)], F(2) ** 200)
st0 = {'W': N, 'marks': [{'t': 'G', 'p': cpos(1)}, {'t': 'M', 'p': N - 2}], 'lastD': None, 'lastKind': None, 'chain': 0}
roots = []
for par in range(4):                       # N mod 4
    cs = Coset([par], [[4]]); cs.bits = 2
    try: check_tape(st0['W'], st0['marks'], cs, Ctx([]))
    except Stop: continue
    roots.append((par, cs))
print('valid N mod 4:', [r[0] for r in roots])
out = {}
def rec(k, w): o = out.setdefault(k, [F(0), 0]); o[0] += w; o[1] += 1
stack = [(st0, cs, [], [], 0) for _, cs in roots]
while stack:
    st, cs, forced, shapes, rd = stack.pop()
    c2 = cs.copy(); ctx = Ctx(forced)
    try: nx, meets = do_round(st, c2, ctx)
    except Branch:
        if cs.bits + len(forced) + 1 > cut: rec('cut', F(1, 2 ** (cs.bits + len(forced))))
        else: stack.append((st, cs, forced + [0], shapes, rd)); stack.append((st, cs, forced + [1], shapes, rd))
        continue
    except Stop as s: rec('stop:' + s.k, F(1, 2 ** c2.bits)); continue
    except Inconsistent: rec('inconsistent', F(1, 2 ** c2.bits)); continue
    sh = ''.join(m['t'] for m in sorted(nx['marks'], key=lambda q: q['p'].v)); shapes2 = shapes + [sh]; L = len(shapes2); w = F(1, 2 ** c2.bits)
    ms = sorted(nx['marks'], key=lambda q: q['p'].v)
    if L >= 3 and shapes2[-3:] == ['GWWW', 'GBW', 'GMB']: rec('plain entry', w); print('   entry path:', ' '.join(shapes2)); continue
    if rd >= 1 and len(ms) == 3 and ms[1]['t'] == 'M' and ms[2]['t'] == 'M' and ES.iszero(ms[2]['p'] - (nx['W'] - 2)): rec('segment ends at GMM', w); continue
    if len(ms) == 2 and ms[1]['t'] == 'M' and ES.iszero(ms[1]['p'] - (nx['W'] - 2)): rec('clean tape', w); continue
    if L > 200: rec('limit', w); continue
    stack.append((nx, c2, [], shapes2, rd + 1))
tot = sum(v[0] for v in out.values())
print('total measure (of all N):', float(tot))
for k, (ms, n) in sorted(out.items()): print(f'  {k}: measure {float(ms):.6g} ({n} paths)')
