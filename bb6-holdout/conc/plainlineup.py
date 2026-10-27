"""Same check for the plain loop: at the first pass start of a long run, the line of the class at its entry depth;
for m = 1..5, can any member complete m passes?"""
import sys, io, contextlib
from fractions import Fraction as F
from conc import Model, Pos
with contextlib.redirect_stdout(io.StringIO()):
    from cyccost import setup, CYC, outs
from k1lineup import solve1d
def forced_plain(m, vals):
    big = [F(v) * 2 ** (4 * m + 120) for v in vals]
    md = setup(big, False); md.force = outs * m
    for c in range(m):
        for want in CYC:
            md.do_round()
            if md.bad or md.shape() != want: return None
    return md.cong
def entry_line(n0, target_round, nv):
    for k in range(8, 60):
        rho = n0 % (1 << k)
        m = Model(1); m.W = Pos([F(2 ** (k + 1)), F(2 * rho + 6)], 2 * n0 + 6); m.add('G', m.const(1)); m.add('M', m.W - 2)
        ok = True
        for r in range(1, target_round + 1):
            nc = len(m.cong); m.do_round()
            for (d, res, mod) in m.cong[nc:]:
                if d.f[0].denominator != 1 or int(d.f[0]) % 4: ok = False
            if not ok: break
        if ok:
            mk = m.marks(); pos = [p for t, p in mk[1:]] + [m.W]
            return k, [(int(p.f[0]), int(p.f[1])) for p in pos], [p.v for p in pos]
for l in (list(open(sys.argv[1]))[:int(sys.argv[2])] if __name__ == '__main__' else []):
    n0 = int(l.split()[0]); w0 = 2 * n0 + 6
    m = Model(1); m.W = m.const(w0); m.add('G', m.const(1)); m.add('M', m.W - 2); hist = []
    for r in range(1, 4000):
        m.do_round(); hist.append(m.shape())
        if len(hist) >= 3 and hist[-3] == 'GWWW' and hist[-2] == 'GBW' and hist[-1] == 'GMB': break
    rps = len(hist) - 2
    e = entry_line(n0, rps, 4)
    k, fm, vv = e
    alpha = [a for a, b in fm]; beta = [b for a, b in fm]
    res = []
    for mm in range(1, 6):
        cg = forced_plain(mm, vv)
        res.append('geo' if cg is None else ('-' if solve1d(cg, alpha, beta) is None else 'yes'))
    print(n0, f"entry depth {k}, pass start round {rps}: m=1..5:", ' '.join(res), flush=True)
