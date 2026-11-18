"""Tests of bbtools.rleaccel_rec (cycle rules whose proofs use earlier rules): the accelerated run must agree exactly,
tape, state and step count, with a direct run, also after level-2 rules have been applied.

usage: python3 tools/tests/test_rleaccel_rec.py
"""
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "py"))

from bbtools.rleaccel_rec import RecSim, Poly, faulhaber, sum_over_cycles  # noqa: E402
from test_rleaccel import MACHINES, BB5, direct, cells  # noqa: E402

# holdouts where level-2 rules occur in the first 3*10^5 steps
LEVEL2 = ["1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD", "1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---"]


class T(unittest.TestCase):
    def check(self, m, k, target):
        s = RecSim(m, k)
        s.run(10 ** 9, stop=target)
        self.assertIsNone(s.halted)
        self.assertIsNone(s.nonhalt)
        kind, n, tape = direct(m, s.steps)
        self.assertEqual(kind, "run")
        d = "".join(str(tape.get(i, 0)) for i in range(min(tape), max(tape) + 1)).strip("0")
        self.assertEqual(d, cells(s), (m, k, target))
        return s

    def test_level2_against_direct(self):
        n2 = 0
        for m in LEVEL2:
            s = self.check(m, 2, 300000)
            n2 += s.levels.get(2, 0)
        self.assertGreater(n2, 10)

    def test_plain_machines(self):
        for m in MACHINES:
            for k in (1, 2):
                self.check(m, k, 100000)

    def test_halt(self):
        s = RecSim(BB5, 2)
        s.run(10 ** 9)
        self.assertIsNotNone(s.halted)
        self.assertEqual(s.steps, 47176870)

    def test_sums(self):
        for e in range(6):
            a = faulhaber(e)
            for k in range(8):
                self.assertEqual(sum(j ** e for j in range(k)), sum(c * k ** i for i, c in enumerate(a)))
        # sum_{j<k} (x0 + 2j) * (x1 - j) at x0 = 5, x1 = 40, k = 7
        P = Poly({(0, 1): 1})
        got = sum_over_cycles(P, {0: Poly.of(5), 1: Poly.of(40)}, [2, -1], 7).const()
        self.assertEqual(got, sum((5 + 2 * j) * (40 - j) for j in range(7)))


if __name__ == "__main__":
    unittest.main()
