"""How late can a run enter the plain loop after extra-wall passes? (October 22)

Start from an extra-wall pass start G 1, W a, W b, W c, W d with end E, every position free (gaps large), and follow
every branch of the same run (stepper engine rules and checks, endsym.do_round) through at most MMAX completed
extra-wall passes (P, Q, or any 8-round word that returns to G W W W W ... we count completed P and Q passes) until the
run reaches a phase-0 plain pass start (G W W W followed by G B W and G M B), breaks, or hits the cut.

At each plain entry the end distance R1 = W - c' - 1 and the countdown L1 = 147b' + 280W - 392c' - 578 are affine forms
in the start state.  Written in the start state's gaps t1 = a, t2 = b - a, t3 = c - b, t4 = d - c, t5 = E - d
(R2 = t5 - 1 is the extra-wall right countdown), R1 = sum beta_j t_j + beta_0 with every beta_j >= 0 (chain lemma).

usage: python3 xdrop.py MMAX CUT [geometry]
"""
import sys, math, itertools, collections
from fractions import Fraction as F
import endsym as ES
ES.NV = 5
from endsym import Pos, cpos, Coset, Ctx, check_tape, do_round, Stop, Branch, Inconsistent

PASS_P = ['GBWW', 'GWWWW', 'GBWW', 'GMBW', 'GMWWW', 'GMBW', 'GMWWW', 'GWWWW']
PASS_Q = ['GBWW', 'GMMWW', 'GMWWW', 'GMBW', 'GMWWW', 'GMBW', 'GMWWW', 'GWWWW']
GEOS = [(200, 5000, 9000, 9700, 10000), (100, 3000, 8000, 9900, 10000), (500, 6000, 9500, 9800, 10000),
        (50, 4000, 7000, 9000, 10000)]


def gaps(form):
    """affine form over (a, b, c, d, E) -> coefficients on the gaps t1..t5 (suffix sums) and the constant"""
    al = form[:5]
    return [sum(al[k] for k in range(j, 5)) for j in range(5)], form[5]


def run(MMAX, cut, geo):
    SC = F(2) ** 200
    vals = [F(x) * SC for x in GEOS[geo]]
    var = lambda i: Pos([F(int(i == j)) for j in range(5)] + [F(0)], vals[i])
    a, b, c, d, E = (var(i) for i in range(5))
    st0 = {'W': E, 'marks': [{'t': 'G', 'p': cpos(1)}, {'t': 'W', 'p': a}, {'t': 'W', 'p': b}, {'t': 'W', 'p': c},
                             {'t': 'W', 'p': d}], 'lastD': None, 'lastKind': None, 'chain': 0}
    roots = []
    for par in itertools.product((0, 1), repeat=5):
        cs = Coset(list(par), [[2 * (i == j) for j in range(5)] for i in range(5)])
        try: check_tape(st0['W'], st0['marks'], cs, Ctx([]))
        except Stop: continue
        roots.append(cs)
    tally = collections.Counter(); mass = collections.defaultdict(F)
    entries = []                      # (weight, m, word, R1 gaps, L1 gaps)
    stack = [(st0, cs, [], [], [], 0) for cs in roots]
    nroot = len(roots)
    while stack:
        st, cs, forced, shapes, states, m = stack.pop()
        c2 = cs.copy(); ctx = Ctx(forced)
        try:
            nx, meets = do_round(st, c2, ctx)
        except Branch:
            if cs.bits + len(forced) + 1 > cut:
                tally['cut'] += 1; mass['cut'] += F(1, 2 ** (cs.bits + len(forced)))
            else:
                stack.append((st, cs, forced + [0], shapes, states, m)); stack.append((st, cs, forced + [1], shapes, states, m))
            continue
        except Stop as s:
            tally[s.k] += 1; mass[s.k] += F(1, 2 ** c2.bits); continue
        except Inconsistent:
            tally['inconsistent'] += 1; mass['inconsistent'] += F(1, 2 ** c2.bits); continue
        sh = ''.join(mk['t'] for mk in sorted(nx['marks'], key=lambda q: q['p'].v))
        shapes2 = shapes + [sh]; states2 = states + [nx]; L = len(shapes2); w = F(1, 2 ** c2.bits)
        if (L == 1 and sh != 'GBWW') or (L == 2 and sh not in ('GWWWW', 'GMMWW')):
            tally['notpass'] += 1; mass['notpass'] += w; continue
        m2 = m
        if L >= 8 and (L == 8 or shapes2[L - 9] == 'GWWWW') and shapes2[L - 8:] in (PASS_P, PASS_Q):
            m2 = m + 1
            if m2 > MMAX: tally['more passes'] += 1; mass['more passes'] += w; continue
        if L >= 3 and shapes2[L - 3:] == ['GWWW', 'GBW', 'GMB']:
            s0 = states2[L - 3]; mk = sorted(s0['marks'], key=lambda q: q['p'].v)
            bb, cc, W0 = mk[2]['p'], mk[3]['p'], s0['W']
            R1 = W0 - cc - 1
            L1f = [147 * x + 280 * y - 392 * z for x, y, z in zip(bb.f, W0.f, cc.f)]; L1f[-1] -= 578
            entries.append((w, m2, ' '.join(shapes2[:L - 2]), gaps(list(R1.f)), gaps(L1f)))
            tally['plain entry'] += 1; mass['plain entry'] += w; continue
        if L > 90: tally['limit'] += 1; mass['limit'] += w; continue
        stack.append((nx, c2, [], shapes2, states2, m2))
    return tally, mass, entries, nroot


if __name__ == '__main__':
    MMAX, cut = int(sys.argv[1]), int(sys.argv[2]); geo = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    tally, mass, entries, nroot = run(MMAX, cut, geo)
    print(f"start parity classes {nroot}; outcomes (paths, measure per class):")
    for k in tally: print(f"  {k}: {tally[k]} paths, {float(mass[k] / nroot):.4g}")
    bym = collections.defaultdict(list)
    for e in entries: bym[e[1]].append(e)
    for mm in sorted(bym):
        es = bym[mm]
        print(f"plain entries after {mm} extra-wall passes: {len(es)} paths, measure {float(sum(e[0] for e in es) / nroot):.4g}")
        # group by R1 gap coefficients
        grp = collections.defaultdict(lambda: [F(0), 0, None, set()])
        for w, m_, word, (rb, r0), (lb, l0) in es:
            key = tuple(rb)
            g = grp[key]; g[0] += w; g[1] += 1; g[3].add(tuple(lb))
            if g[2] is None: g[2] = word
        for key, (wt, n, word, lset) in sorted(grp.items(), key=lambda kv: -kv[1][0])[:12]:
            print(f"   R1 = {' + '.join(f'{x}*t{j+1}' for j, x in enumerate(key) if x)}  (measure {float(wt / nroot):.3g}, {n} paths, "
                  f"{len(lset)} L1 forms, e.g. L1 = {' + '.join(f'{x}*t{j+1}' for j, x in enumerate(next(iter(lset))) if x)}); {word}")
    import pickle
    pickle.dump((tally, dict(mass), entries, nroot), open(f'xdrop_m{MMAX}_c{cut}_g{geo}.pkl', 'wb'))
