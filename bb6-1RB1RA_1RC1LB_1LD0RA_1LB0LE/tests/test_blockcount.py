"""The 7-block excursion of py/blockcount.py and lean/Seven.lean, on the Python closed form.

usage: python3 bb6-1RB1RA_1RC1LB_1LD0RA_1LB0LE/tests/test_blockcount.py
"""
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "py"))

import blockcount as B  # noqa: E402
import passmap  # noqa: E402
from invsearch import psi, psi_step  # noqa: E402


class TestBlockCount(unittest.TestCase):
    def test_witness(self):
        """a = 2^203 + 2^221 + 1 = 5 mod 12: 7 blocks after 204 passes, back at [a+288, ...] after 216."""
        a = B.WITNESS
        self.assertEqual(a % 12, 5)
        ex = B.excursion(a)
        self.assertEqual(len(ex) - 1, 216)
        self.assertEqual(ex[-1], [a + 288, 2 * (a + 288) + 1])
        self.assertEqual([t for t, y in enumerate(ex) if len(y) >= 7], [204])
        self.assertEqual(max(len(y) for y in ex), 7)
        self.assertGreater(min(min(y) for y in ex), 2 ** 18)

    def test_route(self):
        """The route to 7 blocks is the escape the (k, psi) graph allows: (4,3) (5,-17) (4,11) (5,-21) (5,-5)
        (6,23) (6,9) (7,-56), and psi follows psi_step on every pass."""
        ex = B.excursion(B.WITNESS)
        route = [(len(y), psi(y), passmap.stop_index(y)) for y in ex[197:205]]
        self.assertEqual(route, [(4, 3, 1), (5, -17, 3), (4, 11, 1), (5, -21, 2), (5, -5, 1), (6, 23, 2),
                                 (6, 9, 1), (7, -56, 7)])
        for y, z in zip(ex[:-1], ex[1:]):
            self.assertEqual(psi(z), psi_step(psi(y), len(y) - passmap.stop_index(y)))

    def test_loose(self):
        """The sentinel orbit from [1, 3] has 6 blocks with odd psi at pass 203 (psi = 9): the state the
        classes to mod 2^66 never reach."""
        first = B.loose_firsts(210)
        self.assertEqual(first[6][0], 202)
        y = [1, 3]
        for _ in range(203):
            y = B.loose_step(y)
        self.assertEqual((len(y), psi(y)), (6, 9))

    def test_powers(self):
        """Among a = 2^r + 1, r < 210, only r = 203 (a = 9 mod 12) reaches 7 blocks, at pass 204."""
        self.assertEqual(B.powers(210), [(203, 9, 204, 7)])


if __name__ == "__main__":
    unittest.main()
