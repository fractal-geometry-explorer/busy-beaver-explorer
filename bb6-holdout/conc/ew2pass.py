"""For GMM-born routes into G W W W W that allow one pass, show the state after the pass and the first condition
of a second pass that the coset violates."""
import sys, json
from fractions import Fraction as F
import ewforms as EF, mixsolve as MS
import ewroutes as EW
routes = json.load(open(sys.argv[1]))
P5 = {x: EF.pass5(x) for x in 'PQ'}
for idx, (h, o, p) in enumerate(routes):
    for first in 'PQ':
        if EW.consistent(h, o, first) != 'ok': continue
        shapes = list(h) + (MS.P_sh if first == 'P' else MS.Q_sh)
        outs = list(o) + (MS.P_out if first == 'P' else MS.Q_out)
        md = EF.route_model(shapes, outs)
        C = EF.coset_from(md.cong)
        mk = md.marks(); wpos = [q for t, q in mk[1:]] + [md.W]
        print(f"#{idx} after {first}: coset 2^{C.index_bits():.0f}; walls " + ' | '.join(EF.show(q.f) for q in wpos))
        for letter in 'PQ':
            C2 = EF.coset_from(md.cong)
            for k, (form5, res, mod) in enumerate(P5[letter]):
                f = EF.subst(form5, wpos); M, c, den = EF.frac_row(f, 2)
                if not C2.impose(M, den * res - c, den * mod, reduce=False):
                    print(f"    second {letter}: condition {k + 1} fails: {EF.show5(form5.f)} = {res} mod {mod}  [{EF.show(f)}]"); break
            else: print(f"    second {letter}: consistent")
