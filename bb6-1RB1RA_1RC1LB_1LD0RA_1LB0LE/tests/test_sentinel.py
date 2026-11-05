"""Checks on py/sentinel.py: the sentinel conjugacy of lean/Sentinel.lean on the Python closed form, the sentinel
orbit as phi of the blank orbit, the inner counter, and the excursions from a = 1 + 2^m u running the blank orbit
(CI runs them, .github/workflows/tests.yml).

usage: python3 bb6-1RB1RA_1RC1LB_1LD0RA_1LB0LE/tests/test_sentinel.py
"""
import os
import random
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "py"))

import induction  # noqa: E402
import passmap  # noqa: E402
import returnmap  # noqa: E402
import sentinel  # noqa: E402


class TestSentinel(unittest.TestCase):
    def test_conjugacy(self):
        """`next_phi`: passmap(phi(y)) = phi(passmap(y)) on random lists, halts and stops at a block of 1 included."""
        ev = sentinel.conj(30000)
        self.assertGreater(ev.get("HALT", 0), 100)
        self.assertGreater(ev.get("None", 0), 100)

    def test_sentinel_orbit(self):
        """`sentinel_orbit`: from [5, 3] the closed form runs phi of the blank orbit; and that is the loose orbit
        from [1, 3] of py/induction.py after its first pass ([0, 5, 3])."""
        y = [5, 3]
        orb = sentinel.blank_orbit(3000)
        for t in range(1, 3000):
            y = passmap.passmap(y)
            self.assertEqual(y, sentinel.phi(orb[t]), t)
        e = induction.loose([1, 3])
        self.assertEqual(e, [0, 5, 3])
        for t in range(1, 300):
            e = induction.loose(e)
            while e[0] == 0:
                e = e[1:]
            self.assertEqual(e, sentinel.phi(orb[t]), t)

    def test_inner_counter(self):
        """`inner_counter`: [x, 2x+6, 3] returns to [x', 2x'+6, 3] after exactly the passes [x, 2x+1] takes to x'."""
        for x in range(5, 4000, 4):
            g, n, _ = returnmap.G(x)
            y = [x, 2 * x + 6, 3]
            for _ in range(n):
                y = passmap.passmap(y)
            self.assertEqual(y, [g, 2 * g + 6, 3], x)

    def test_deep(self):
        """For a = 1 + 2^m u the first m - 1 passes are phi(blank orbit) modulo 2^(m-t-1), with the same sweeps, and
        the first block stays at least a/4 after pass 5."""
        rnd = random.Random(7)
        for m in (20, 33, 64, 150, 600):
            orb = sentinel.blank_orbit(m)
            for i in range(6):
                u = 1 if i == 0 else 2 * rnd.getrandbits(40) + 1
                low, _ = sentinel.deep(m, u, orb)
                self.assertGreaterEqual(low, 0.2497, (m, u))

    def test_open_classes_start_with_the_blank_orbit(self):
        """Every open class mod 2^28 has v2(a - 1) >= 8, and its excursion starts with the inner value 5, the blank
        orbit's first state [5, 11]."""
        for a in sentinel.open_members(26, 40):
            self.assertGreaterEqual(sentinel.v2(a - 1), 8)
            xs, end = sentinel.inner_values(a)
            self.assertEqual(xs[0], (1, 5), a)
            self.assertIsInstance(end, int)


if __name__ == "__main__":
    unittest.main()
