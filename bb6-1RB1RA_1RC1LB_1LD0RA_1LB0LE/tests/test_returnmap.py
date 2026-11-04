"""Checks on the return map on two-block states (py/returnmap.py; CI runs them, .github/workflows/tests.yml).

usage: python3 bb6-1RB1RA_1RC1LB_1LD0RA_1LB0LE/tests/test_returnmap.py
"""
import os
import random
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "py"))

import passmap  # noqa: E402
import returnmap  # noqa: E402


class TestReturnMap(unittest.TestCase):
    def test_chains(self):
        """The six short chains hold on their whole classes mod 4."""
        self.assertTrue(returnmap.check_chains())

    def test_chains_concrete(self):
        for d, (r, s, d2, n) in returnmap.CHAINS.items():
            for a in range(r + 8, 400, 4):
                y = [a, 2 * a + d]
                for _ in range(n):
                    y = passmap.passmap(y)
                self.assertEqual(y, [a + s, 2 * (a + s) + d2], (a, d))

    def test_classes(self):
        """Down to a mod 2^38: no bad class, only a = 1 set aside, every route ends at a + 12k after 9k passes, and
        the members of the open classes below 2^38 return too."""
        byk, leaves, open_, points, bad, concrete = returnmap.classes(36)
        self.assertEqual(bad, [])
        self.assertEqual(points, [1])
        self.assertEqual(sorted(byk.items())[:4], [(1, 5), (2, 20), (3, 36), (4, 130)])
        for a, (g, n, small) in concrete.items():
            if a != 1:
                self.assertIsNotNone(g, a)
                self.assertEqual(n, 9 * ((g - a) // 12))

    def test_classes_agree_with_concrete(self):
        """Random members of the leaf classes follow their class's route to its end under the plain closed form."""
        leaves, _, _, _ = returnmap.explore(lambda a: [a, 2 * a + 1], [returnmap.Aff(1, 4)], returnmap.two_block(1), 20)
        rnd = random.Random(3)
        items = list(leaves.items())
        for (ends, route), cl in rnd.sample(items, min(200, len(items))):
            a = cl[0][0].at(rnd.randint(0, 10 ** 6))
            g, n, small = returnmap.G(a)
            self.assertEqual((g - a, n), (ends[0], len(route)), a)

    def test_concrete(self):
        """G(a) = a + 12k after 9k passes for a = 5, 9, ..., 40001."""
        for a in range(5, 40002, 4):
            g, n, small = returnmap.G(a)
            self.assertIsNotNone(g, a)
            self.assertEqual(((g - a) % 12, n), (0, 9 * ((g - a) // 12)), a)

    def test_orbit(self):
        """From pass 3 ([5, 11]) on, the orbit's states [a, 2a+1] have a = 5 mod 12 and each follows from the last
        by G; the passes between them hold no other such state."""
        r = returnmap.orbit_returns(30000)
        self.assertEqual(r[0], (3, 5))
        for (i, a), (i2, a2) in zip(r, r[1:]):
            self.assertEqual(a % 12, 5)
            g, n, _ = returnmap.G(a)
            self.assertEqual((g, n), (a2, i2 - i))


if __name__ == "__main__":
    unittest.main(verbosity=2)
