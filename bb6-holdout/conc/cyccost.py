from conc import *
from snf2 import bits_fixed, solve_info
from fractions import Fraction as F
CYC = ['GBW', 'GMB', 'GMWW', 'GMB', 'GMWW', 'GWWW', 'GBW', 'GWWW']
E0, r0, R0 = map(int, open('cyc_starts.txt').readline().split())
# concrete: one round to reach GWWW
m0 = Model(1); m0.W = m0.const(E0); m0.add('G', m0.const(1)); m0.add('B', m0.const(r0)); m0.add('W', m0.const(R0)); m0.do_round()
mk = m0.marks(); assert m0.shape() == 'GWWW'
vals = [p.v for t, p in mk[1:]] + [m0.W.v]
print("GWWW state:", vals)
names = ['a', 'b', 'c', 'E']
def setup(scale_vals, concrete):
    m = Model(4)
    for i, (t, x) in enumerate(zip('WWW', scale_vals[:3])): m.add(t, m.var(i, x) if concrete else Pos(m.var(i, 0).f, F(x)))
    m.W = m.var(3, scale_vals[3]) if concrete else Pos(m.var(3, 0).f, F(scale_vals[3]))
    m.add('G', m.const(1)); return m
# concrete pass over one cycle to get the outcome sequence
m = setup(vals, True); outs = []
for rd, want in enumerate(CYC):
    m.do_round(); assert m.shape() == want, (rd, m.shape())
outs = m.outcomes[:]
print("outcomes per cycle:", outs, " tests:", len(outs))
print("bits for one cycle:", bits_fixed(m.cong, 4))
for t, p in m.marks()[1:]: print("   ", t, fmt(p, names))
print("    end", fmt(m.W, names))
# forced: m cycles, geometry from a scaled-up point
big = [F(v) * 2**200 for v in vals]
for ncyc in range(1, 9):
    m = setup(big, False); m.force = outs * ncyc
    ok = True
    for c in range(ncyc):
        for want in CYC:
            m.do_round()
            if m.shape() != want or m.bad: ok = False; break
        if not ok: break
    if not ok: print(ncyc, "cycles: geometry broke", m.shape(), m.bad); break
    b, ok, S = solve_info(m.cong, 4)
    print(f"{ncyc} cycles: tests {len(m.cong)}, bits fixed {b}, solvable {ok} (modulus 2^{S})")
