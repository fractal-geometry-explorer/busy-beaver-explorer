"""For a clean-tape run sustained by the 8-round cycle: the right target t_R (the end distance d_1 = -2 exactly, so
every end meeting merges) and the left target t_L (the 2-adic n whose left clocks keep the cycle going, with the
right-end tests assumed).  The run length should follow v2(t_L - t_R)."""
import sys
from fractions import Fraction as F
from tree4 import TModel, Coset, Pos
from cyccost import outs, CYC
from snf2 import v2
n0 = int(sys.argv[1]); s0 = int(sys.argv[2]); R_ENTRY = int(sys.argv[3]); NCYC = int(sys.argv[4])
w0 = 2 * n0 + 6
class M2(TModel):
    def test_outcome(self, d):
        val = int(d.f[0] * w0 + d.f[1])
        if self.phase == 0:
            dec = self.coset.decided(d.f)
            if dec is None: self.coset.impose(d.f, val % 4)
            return val % 4
        res = self.fq.pop(0)
        if self.cur_last: self.endforms.append(d); return res
        dec = self.coset.decided(d.f)
        if dec is None: self.coset.impose(d.f, res)
        elif dec != res: self.conflict.append((self.rd, d)); 
        return res
m = M2(1); m.W = Pos([F(1), F(0)], F(w0)); m.add('G', m.const(1)); m.add('M', Pos([F(1), F(-2)], F(w0 - 2)))
c = Coset([w0], [[2 ** (s0 + 1)]]); m.setup_tree(c); m.phase = 0; m.endforms = []; m.conflict = []
for rd in range(R_ENTRY): m.do_round()
print("entry shape", m.shape(), "bits", c.bits)
# geometry: switch the concrete values to a scaled-up virtual point so that halvings stay valid
m.phase = 1; m.fq = outs * NCYC
for k in range(NCYC):
    for want in CYC:
        m.do_round()
        assert m.shape() == want, (m.shape(), want)
    tL = c.x0[0] % c.B[0][0]; modb = v2(c.B[0][0])
    print(f" after {k+1} cycles: left target known mod 2^{modb}; conflicts {len(m.conflict)}")
d1 = m.endforms[0]
print("first right-end form of the cycle:", d1.f)
# t_R : d1(N) = -2  -> N = (-2 - c)/a in Z_2, mod 2^modb
a, cc = d1.f; num = -2 - cc
MODB = 2 ** modb
an, ad = a.numerator, a.denominator; cn, cd = num.numerator, num.denominator
# N = num/a = (cn/cd) * (ad/an)
tR = (cn * ad * pow(cd * an, -1, MODB * 2**20)) % (MODB)
NR = w0
print(f"v2(N0 - t_L) = {v2((w0 - tL) % MODB) if (w0 - tL) % MODB else '>= ' + str(modb)},  v2(N0 - t_R) = {v2((w0 - tR) % MODB)},  v2(t_L - t_R) = {v2((tL - tR) % MODB)}")
