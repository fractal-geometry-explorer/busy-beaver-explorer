import sys
from fractions import Fraction as F
from tree4 import TModel, Coset, Pos
def entry_bits(n0, R):
    w0 = 2 * n0 + 6
    class FM(TModel):
        def test_outcome(self, d):
            dec = self.coset.decided(d.f); val = int(d.f[0] * w0 + d.f[1])
            if dec is None: self.coset.impose(d.f, val % 4)
            return val % 4
    m = FM(1); m.W = Pos([F(1), F(0)], F(w0)); m.add('G', m.const(1)); m.add('M', Pos([F(1), F(-2)], F(w0 - 2)))
    c = Coset([w0], [[2]]); m.setup_tree(c)
    for r in range(R): m.do_round()
    return c.bits
if __name__ == '__main__':
    print(entry_bits(int(sys.argv[1]), int(sys.argv[2])))
