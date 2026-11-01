"""Checks on py/induction.py: the free-parity obstruction and the sentinel orbit near a = 1 (CI runs them,
.github/workflows/tests.yml).

usage: python3 bb6-1RB1RA_1RC1LB_1LD0RA_1LB0LE/tests/test_induction.py
"""
import os
import random
import sys
import unittest
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "py"))

import induction  # noqa: E402
import passmap  # noqa: E402


class TestInduction(unittest.TestCase):
    def test_free_halves(self):
        """With free parities the first block falls to 1/6, 1/12, 1/24, 1/48, then halves every two passes."""
        mins = induction.free(9)
        self.assertEqual(mins, [Fraction(1, 6), Fraction(1, 12), Fraction(1, 24), Fraction(1, 48), Fraction(1, 48),
                                Fraction(1, 96), Fraction(1, 96), Fraction(1, 192), Fraction(1, 192)])

    def test_free_step_is_the_closed_form_scaled(self):
        """The free step with the true parities is the closed form up to the constants: blocks within 3 per pass."""
        rnd = random.Random(1)
        for _ in range(2000):
            y = [rnd.randrange(2, 10 ** 6) for _ in range(rnd.randrange(2, 6))]
            out = passmap.passmap(y)
            if not isinstance(out, list):
                continue
            f = induction.free_step([float(v) for v in y], [v % 2 for v in y])
            if len(f) != len(out):
                continue
            self.assertTrue(all(abs(a - b) <= 3 for a, b in zip(f, out)), (y, f, out))

    def test_loose_is_passmap(self):
        """`loose` is the closed form wherever the closed form gives a list (up to leading zeros)."""
        rnd = random.Random(2)
        for _ in range(5000):
            y = [rnd.randrange(1, 40) for _ in range(rnd.randrange(1, 6))]
            out = passmap.passmap(y)
            if isinstance(out, list) and passmap.stop_index(y) >= 1:
                e = induction.loose(y)
                while e and e[0] == 0:
                    e.pop(0)
                self.assertEqual(e, out, y)

    def test_sentinel(self):
        """a = 2^m + 1 follows the sentinel orbit from [1, 3] modulo a shrinking power of two; the inner counter
        [x, 2x+6, 3] steps by 12."""
        for m in (60, 120):
            inner = induction.sentinel(m, m - 13)
            xs = [x for _, x, d in inner if d == 6]
            self.assertEqual(xs[:5], [5, 17, 29, 41, 53])

    def test_sentinel_other_u(self):
        """Any a = 1 + 2^m u with u odd follows the same sentinel orbit (the bits above m are not read early)."""
        m, n, slack = 100, 80, 12
        rnd = random.Random(3)
        for _ in range(5):
            a = 1 + 2 ** m * (2 * rnd.randrange(1, 10 ** 6) + 1)
            y, e = [a, 2 * a + 1], [1, 3]
            for t in range(n):
                y, e = passmap.passmap(y), induction.loose(e)
                e = e[len(e) - len(y):]
                mod = 2 ** (m - t - slack)
                self.assertTrue(all((v - w) % mod == 0 for v, w in zip(y, e)), (a, t))

    def test_psi_rule(self):
        """lean/Psi.lean, `psi_next`: with psi = y_k - 2 y_(k-1) + 4 y_(k-2) - ..., a pass gives
        2 psi' = -psi + 3 (-2)^n - 7, n the number of blocks crossed (k - j, 0 for an even last block)."""
        def psi(y):
            s = 0
            for v in y:
                s = v - 2 * s
            return s
        rnd = random.Random(4)
        for _ in range(20000):
            y = [rnd.randrange(1, 60) for _ in range(rnd.randrange(1, 8))]
            out = passmap.passmap(y)
            if isinstance(out, list):
                n = len(y) - passmap.stop_index(y)
                self.assertEqual(2 * psi(out), -psi(y) + 3 * (-2) ** n - 7, y)


if __name__ == "__main__":
    unittest.main(verbosity=2)
