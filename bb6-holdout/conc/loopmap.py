"""Affine map and contracting directions of a loop of shapes found inside GMM-born routes.
Take a route containing the loop twice; read the outcomes of one loop period; run the loop on a generic state with
free positions; print the map, its rational eigenvalues/eigenforms and the number of congruences per period."""
import sys, json
from fractions import Fraction as F
from conc import Model, Pos
from ewmap import nullspace, charpoly_roots

def per_round_outs(shapes, outs, ratio):
    E_ex = 2 ** 40 + 1; m_ex = int(E_ex * ratio) // 2 * 2; sc = F(2) ** 140
    md = Model(2); md.W = Pos([F(0), F(1), F(0)], F(E_ex) * sc)
    md.add('G', md.const(1)); md.add('M', Pos([F(1), F(0), F(0)], F(m_ex) * sc)); md.add('M', md.W - 2)
    md.force = list(outs); cuts = [0]; states = []
    for want in shapes:
        states.append(md.marks())
        md.do_round(); assert md.shape() == want, (md.shape(), want); cuts.append(len(md.outcomes))
    return [outs[cuts[i]:cuts[i + 1]] for i in range(len(shapes))], states, md

def generic_loop(start_shape, loop_shapes, loop_outs, geo):
    """start state of shape start_shape (G at 1, then marks at free positions, end W free); geo = real positions."""
    n = len(start_shape) - 1 + 1          # marks after G, plus W
    md = Model(n)
    types = start_shape[1:]
    for i, t in enumerate(types):
        if i == len(types) - 1 and t == 'M':   # end marker at W - 2
            continue
        md.add(t, Pos([F(int(j == i)) for j in range(n)] + [F(0)], geo[i]))
    md.W = Pos([F(int(j == n - 1)) for j in range(n)] + [F(0)], geo[-1])
    md.add('G', md.const(1))
    if types[-1] == 'M': md.add('M', md.W - 2)
    md.force = [x for o in loop_outs for x in o]
    for want in loop_shapes:
        md.do_round()
        if md.bad or md.shape() != want: return None, f"got {md.shape()} want {want}"
    return md, None

if __name__ == '__main__':
    routes = [json.loads(l) for l in open(sys.argv[1])]
    loop = sys.argv[2].split(',')          # e.g. GMWMM,GWWMM,GBMM
    L = len(loop)
    for r in routes:
        sh = r['shapes']
        for i in range(len(sh) - 2 * L):
            if sh[i:i + L] == loop and sh[i + L:i + 2 * L] == loop: break
        else: continue
        po, states, _ = per_round_outs(sh, r['outs'], r['ratio'])
        start = states[i + 1]               # marks at the start of the round that produces loop[1]... use state before loop[0]
        # state before the round that produces sh[i+1] is the state with shape sh[i]
        st = states[i + 1]
        shape0 = ''.join(t for t, p in st)
        assert shape0 == sh[i], (shape0, sh[i])
        lp = sh[i + 1:i + 1 + L]; lo = po[i + 1:i + 1 + L]
        geo = [p.v for t, p in st[1:]]
        # W value: reconstruct from end marker if present
        Wv = st[-1][1].v + 2 if st[-1][0] == 'M' else None
        geo = geo[:-1] + [Wv] if st[-1][0] == 'M' else geo + [None]
        print("loop start shape", shape0, "period shapes", lp, "outcomes", lo)
        md, err = generic_loop(shape0, lp, lo, geo if st[-1][0] == 'M' else geo)
        if md is None: print("generic run failed:", err); continue
        mk = md.marks(); pos = [p for t, p in mk[1:]]
        if mk[-1][0] == 'M': pos = pos[:-1]
        pos = pos + [md.W]
        nvar = len(pos)
        M = [[p.f[j] for j in range(nvar)] for p in pos]; t = [p.f[nvar] for p in pos]
        for row, tt in zip(M, t): print("   ", [str(x) for x in row], "+", tt)
        for lam, vecs in charpoly_roots(M):
            for v in vecs: print(f"  eigenvalue {lam}: form {[str(x) for x in v]}")
        print("  congruences per period:", len(md.cong))
        break

def show_state(md):
    for t, p in md.marks(): print("     ", t, [str(x) for x in p.f])
    print("      W", [str(x) for x in md.W.f])
