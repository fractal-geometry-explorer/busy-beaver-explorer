import json
from fractions import Fraction as F
import ewroutes as EW, ewforms as EF, mixsolve as MS
routes = json.load(open('../ewroutes_22.json'))
for idx, (shapes, outs, meas) in enumerate(routes):
    print(idx, {w: EW.consistent(shapes, outs, w) for w in ['P', 'Q', 'PP', 'PQ', 'QP', 'QQ']})
    # compare forms: 2-var run of route + P vs substituted 5-var P forms
    for letter in 'PQ':
        md = EF.route_model(shapes, outs, MS.P_out if letter == 'P' else MS.Q_out)
        n0 = len(md.cong)
        mk = md.marks(); wpos = [p for t, p in mk[1:]] + [md.W]
        for want in (MS.P_sh if letter == 'P' else MS.Q_sh):
            md.do_round()
            if md.bad or md.shape() != want: print('  ', letter, 'geometry fails at', want, md.shape()); break
        new = md.cong[n0:]
        P5 = MS.forced(letter).cong
        print('  ', letter, 'counts', len(new), len(P5))
        for k, ((pf, r, mo), (f5, r5, m5)) in enumerate(zip(new, P5)):
            fs = EF.subst(f5, wpos)
            if list(pf.f) != fs or r != r5 or mo != m5:
                print('    diff at', k, EF.show(pf.f), r, mo, '|', EF.show(fs), r5, m5); break
