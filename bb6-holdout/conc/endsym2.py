"""Exact endgame of the one-extra-wall loop (October 22), the analogue of endsym.py.

Start from an extra-wall pass start G 1, W a, W b, W c, W d with end E, where the last two walls sit near the end:
R = E - d - 1 and V = d - c are held fixed (along the loop both shrink 16-fold per pass, a Jordan pair), while a, b and
E are free.  The rounds follow the stepper's engine with all its checks (endsym.do_round).  A path stops at d <= 2
(close), at a packet reaching a block, at a break of the end chain with the end far away, at a new extra-wall pass
start (G W W W W followed by G B W W and then G W W W W [pass P] or G M M W W [pass Q]), at a drop into the plain loop
(a phase-0 plain pass start: G W W W, G B W, G M B), or when the start is not followed by G B W W and a P or Q round.

usage: python3 endsym2.py Rmax Vmax [geometry] [free]   -> closing (R, V) classes with the residue of the left countdown
       L2 = -441b + 735c - 2156d + 1652E - 179 that each one requires.
"""
import sys, math
from fractions import Fraction as F
import endsym as ES
FREEV = len(sys.argv) > 4 and sys.argv[4] == 'free'
ES.NV = 4 if FREEV else 3      # variables a, b, E (c and d tied to E), or a, b, c, E with c free
NVV = ES.NV
from endsym import Pos, cpos, Coset, Ctx, check_tape, do_round, Stop, Branch, Inconsistent

GEOS = [(F(238), F(5238), F(10000)), (F(100), F(4000), F(10000)), (F(1000), F(6500), F(10000)), (F(31), F(2900), F(10000))]
CLOSES = []
PASS_P = ['GBWW', 'GWWWW', 'GBWW', 'GMBW', 'GMWWW', 'GMBW', 'GMWWW', 'GWWWW']
PASS_Q = ['GBWW', 'GMMWW', 'GMWWW', 'GMBW', 'GMWWW', 'GMBW', 'GMWWW', 'GWWWW']


def search(R, V, geo=0, cut=60, maxr=80):
    SC = F(2) ** 200
    av, bv, Ev = (x * SC for x in GEOS[geo])
    var = lambda i, v: Pos([F(int(i == j)) for j in range(NVV)] + [F(0)], v)
    if FREEV:
        a, b, c, E = var(0, av), var(1, bv), var(2, (bv + Ev) / 2), var(3, Ev); d = E - (R + 1)
    else:
        a, b, E = var(0, av), var(1, bv), var(2, Ev); d = E - (R + 1); c = d - V
    st0 = {'W': E, 'marks': [{'t': 'G', 'p': cpos(1)}, {'t': 'W', 'p': a}, {'t': 'W', 'p': b}, {'t': 'W', 'p': c},
                             {'t': 'W', 'p': d}], 'lastD': None, 'lastKind': None, 'chain': 0}
    out = {}
    def rec(key, w, extra=None):
        o = out.setdefault(key, [F(0), 0, []]); o[0] += w; o[1] += 1
        if extra is not None and len(o[2]) < 4: o[2].append(extra)
    roots = []
    import itertools
    for par in itertools.product((0, 1), repeat=NVV):
        cs = Coset(list(par), [[2 * (i == j) for j in range(NVV)] for i in range(NVV)])
        try: check_tape(st0['W'], st0['marks'], cs, Ctx([]))
        except Stop: continue
        roots.append(cs)
    if not roots: return None
    stack = [(st0, cs, [], [], []) for cs in roots]
    while stack:
        st, cs, forced, shapes, states = stack.pop()
        c2 = cs.copy(); ctx = Ctx(forced)
        try:
            nx, meets = do_round(st, c2, ctx)
        except Branch:
            if cs.bits + len(forced) + 1 > cut: rec('cut', F(1, 2 ** (cs.bits + len(forced))))
            else:
                stack.append((st, cs, forced + [0], shapes, states)); stack.append((st, cs, forced + [1], shapes, states))
            continue
        except Stop as s:
            w = F(1, 2 ** c2.bits)
            if s.k == 'close':
                rec('close', w, (int(s.text.const()), len(shapes) + 1))
                CLOSES.append((R, V, list(c2.x0), [r[:] for r in c2.B], shapes + ['(close)']))
            elif s.k == 'break': rec('break', w)
            else: rec(s.k, w, (s.text, len(shapes) + 1))
            continue
        except Inconsistent as e:
            rec('inconsistent', F(1, 2 ** c2.bits), str(e)); continue
        sh = ''.join(m['t'] for m in sorted(nx['marks'], key=lambda m: m['p'].v))
        shapes2 = shapes + [sh]; states2 = states + [nx]; L = len(shapes2)
        w = F(1, 2 ** c2.bits)
        if (L == 1 and sh != 'GBWW') or (L == 2 and sh not in ('GWWWW', 'GMMWW')):
            rec('notpass', w, sh); continue
        if L >= 8 and (L == 8 or shapes2[L - 9] == 'GWWWW') and shapes2[L - 8:] in (PASS_P, PASS_Q):
            Rn = nx['W'] - max(nx['marks'], key=lambda m: m['p'].v)['p'] - 1
            rec('xpass', w, ('P' if shapes2[L - 7] == 'GWWWW' else 'Q', int(Rn.const()) if Rn.lin0() else 'far', L - 8)); continue
        if L >= 3 and shapes2[L - 3:] == ['GWWW', 'GBW', 'GMB']:
            s0 = states2[L - 3]; Rn = s0['W'] - max(s0['marks'], key=lambda m: m['p'].v)['p'] - 1
            rec('drop', w, (int(Rn.const()) if Rn.lin0() else 'far', L - 3)); continue
        if L > maxr: rec('limit', w, ' '.join(shapes2[:24])); continue
        stack.append((nx, c2, [], shapes2, states2))
    return out


def L2_class(R, V, x0, B):
    # L2 = -441b + 735c - 2156d + 1652E - 179 with d = E - R - 1 (and c = d - V unless c is free)
    if FREEV: f = [F(0), F(-441), F(735), F(-504), F(2156 * R + 1977)]
    else: f = [F(0), F(-441), F(231), F(1421 * R - 735 * V + 1242)]
    n = NVV
    L0 = f[n] + sum(f[i] * x0[i] for i in range(n))
    g = [sum(f[i] * B[i][k] for i in range(n)) for k in range(n)]
    mod = 0
    for t in g: mod = math.gcd(mod, int(t))
    r0 = int(L0) % mod
    best = None
    for x in range(-mod * 7, mod * 7 + 1):
        if x % mod == r0 and x % 7 == 3 and (best is None or abs(x) < abs(best)): best = x
    return r0, mod, abs(best)


if __name__ == '__main__':
    Rmax, Vmax = int(sys.argv[1]), int(sys.argv[2]); geo = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    tally = {}; nvalid = 0
    for R in range(2, Rmax + 1, 2):
        for V in ([None] if FREEV else range(3, Vmax + 1, 2)):
            out = search(R, V, geo)
            if out is None: continue
            nvalid += 1
            for k, v in out.items():
                t = tally.setdefault(k, [0, 0]); t[0] += 1; t[1] += v[1]
            bad = [k for k in out if k not in ('close', 'break', 'xpass', 'drop', 'notpass')]
            if bad: print('R', R, 'V', V, 'other:', {k: (float(out[k][0]), out[k][2][:2]) for k in bad}, flush=True)
    print('valid (R, V) starts', nvalid, 'outcome kinds (starts with it, paths):', tally)
    worst = {}
    for R, V, x0, B, shapes in CLOSES:
        r0, mod, mn = L2_class(R, V, x0, B)
        val = 3 * math.log2(R) - 2 * math.log2(mn)
        key = (R, V)
        if key not in worst or val > worst[key][0]: worst[key] = (val, r0, mod, mn, ' '.join(shapes))
    rows = sorted(worst.items(), key=lambda kv: -kv[1][0])
    print('closing (R, V) pairs:', len(rows), '; largest R:', max((k[0] for k in worst), default=None), '; largest V:', max((k[1] for k in worst if k[1] is not None), default=None))
    for (R, V), (val, r0, mod, mn, sh) in rows[:25]:
        print(f"R {R} V {V}: L2 = {r0} mod {mod}, smallest |L2| {mn}, 3log2R - 2log2|L2| = {val:.2f}; {sh}")
