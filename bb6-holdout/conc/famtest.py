"""Dimension test: take a real cycle's state of a given shape (its free marks and the width are the unknowns), force the
outcomes the cycle took from there to the extra-wall state, then a pass word; solve the congruences as a lattice coset
in those unknowns, take the point nearest the same geometry scaled to width 2^K, and run the real machine on it."""
import sys, math
from fractions import Fraction as F
from conc import Model, Pos
from lattice import Coset, babai, lll, lg
from mixsolve import P_out, Q_out, P_sh, Q_sh
sys.path.insert(0, '../rec')
import hybsim
def locate(n0, start_shape, target='GWWWW', skip=0):
    m = Model(1); m.W = m.const(2 * n0 + 6); m.add('G', m.const(1)); m.add('M', m.W - 2)
    snaps = []
    for r in range(4000):
        mk = m.marks(); snaps.append((m.shape(), [(t, p.v) for t, p in mk[1:]], m.W.v, len(m.outcomes)))
        if m.shape() == target and r > 0: break
        m.do_round()
    idx = [i for i, s in enumerate(snaps) if s[0] == start_shape]
    i = idx[-1 - skip]
    return snaps[i], m.outcomes[snaps[i][3]: snaps[-1][3]], [s[0] for s in snaps[i + 1:]]
def family(start, outs, shapes, word, tie_end=True):
    sh, marks, W, _ = start
    free = [k for k, (t, p) in enumerate(marks) if not (tie_end and t == 'M' and p == W - 2)]
    nv = len(free) + 1
    sc = 4 * len(word) + 140
    md = Model(nv)
    md.W = Pos([F(int(j == nv - 1)) for j in range(nv)] + [F(0)], F(W) * 2 ** sc)
    md.add('G', md.const(1))
    for k, (t, p) in enumerate(marks):
        if k in free:
            j = free.index(k); md.add(t, Pos([F(int(q == j)) for q in range(nv)] + [F(0)], F(p) * 2 ** sc))
        else:
            md.add(t, md.W - 2)
    md.force = list(outs)
    for x in word: md.force += (P_out if x == 'P' else Q_out)
    for want in shapes:
        md.do_round()
        if md.bad or md.shape() != want: return None, "route geometry"
    for x in word:
        for want in (P_sh if x == 'P' else Q_sh):
            md.do_round()
            if md.bad or md.shape() != want: return None, f"pass {x} geometry ({md.shape()})"
    C = Coset(nv)
    for pform, res, mod in md.cong:
        f = pform.f; den = max(q.denominator for q in f)
        if not C.impose([int(q * den) for q in f[:nv]], den * res - int(f[nv] * den), den * mod, reduce=False): return None, "inconsistent"
    vals = [marks[k][1] for k in free] + [W]
    for j, v in enumerate(vals):
        if not C.impose([int(q == j) for q in range(nv)], v % 2, 2, reduce=False): return None, "parity"
    C.B = lll(C.B)
    return (C, free, vals, marks), None
def try_scale(fam, K):
    C, free, vals, marks = fam
    W = vals[-1]; t = [F(v * 2 ** K, W) for v in vals]
    x = [a + b for a, b in zip(C.x0, babai(C.B, [u - v for u, v in zip(t, C.x0)]))]
    dev = max(abs(float((a - b) / t[-1])) for a, b in zip(x, t))
    if dev > 0.05: return f"no valid point near the geometry (deviation {dev:.2g})"
    mk = [('G', 1)]
    Wn = x[-1]
    for k, (tp, p) in enumerate(marks):
        mk.append((tp, x[free.index(k)] if k in free else Wn - 2))
    try:
        res = hybsim.run(hybsim.config_from(mk, Wn), max_rounds=40 * K + 400, log=lambda *a: None)
    except AssertionError as e:
        return f"invalid tape: {e}"
    return f"{res['result']} {res.get('rule', '')} after {res['rounds']} rounds"
if __name__ == '__main__':
    n0 = int(sys.argv[1]); start_shape = sys.argv[2]; K = int(sys.argv[3]); words = sys.argv[4:]
    start, outs, shapes = locate(n0, start_shape)
    print(f"start {start[0]} with {len(start[1])} marks; route: {' '.join(shapes)}")
    for w in words:
        fam, err = family(start, outs, shapes, w)
        if fam is None: print(f"  word {w or '-'}: {err}"); continue
        C = fam[0]
        bl = [round(lg(sum(a * a for a in v)) / 2, 1) for v in C.B]
        print(f"  word {w or '-'}: {len(fam[1]) + 1} unknowns, coset index 2^{C.index_bits():.1f}, longest basis vector 2^{max(bl)}; at width 2^{K}: {try_scale(fam, K)}")
