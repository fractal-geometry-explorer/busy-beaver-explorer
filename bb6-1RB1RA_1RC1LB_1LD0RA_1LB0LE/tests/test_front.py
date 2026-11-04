"""The statements of lean/Front.lean on the closed form of py/passmap.py, and the first-block measurements of
py/front.py (CI runs them, .github/workflows/tests.yml).

usage: python3 bb6-1RB1RA_1RC1LB_1LD0RA_1LB0LE/tests/test_front.py
"""
import itertools
import os
import random
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "py"))

import front  # noqa: E402
import passmap  # noqa: E402


def lists(rnd, n, kmax, bmax):
    for _ in range(n):
        yield [rnd.randint(1, bmax) for _ in range(rnd.randint(1, kmax))]


class TestFront(unittest.TestCase):
    def test_good_kept(self):
        """`next_good`: a pass keeps every block after the first at least 2."""
        rnd = random.Random(1)
        for y in lists(rnd, 20000, 7, 40):
            if not front.good(y):
                continue
            z = passmap.passmap(y)
            if isinstance(z, list):
                self.assertTrue(front.good(z), (y, z))

    def test_one_front(self):
        """`one_front`: on a Good list a stop block of 1 is the first block, with every other block crossed."""
        for k in range(1, 6):
            for y in itertools.product(range(1, 8), repeat=k):
                y = list(y)
                if front.good(y) and passmap.passmap(y) is None:
                    self.assertEqual(y[0], 1, y)
                    self.assertEqual(passmap.stop_index(y), 1, y)

    def test_front_twice(self):
        """`front_twice`: with 4 | ones, a front stop is never followed by another; with 2 mod 4 it can be."""
        seen2 = False
        for k in range(2, 6):
            for y in itertools.product(range(1, 13), repeat=k):
                y = list(y)
                if not front.front_stop(y):
                    continue
                z = passmap.passmap(y)
                if isinstance(z, list) and front.front_stop(z):
                    self.assertEqual(sum(y) % 4, 2, (y, z))
                    seen2 = True
        self.assertTrue(seen2)

    def test_orbit(self):
        """The first 200,000 passes: Good, no two front stops in a row (asserted inside `stats`), no descent of
        the first block with more than 3 front stops, the first block above 2.7% of the ones after pass 50."""
        depths, deepest, min_ratio = front.stats(200000)
        self.assertLessEqual(max(depths), 3)
        self.assertGreater(min_ratio[0], 0.027)

    def test_loop(self):
        """The examples of the halving loop reach a stop block of 1."""
        for y in front.LOOP_EXAMPLES:
            z = y
            while isinstance(z, list):
                z = passmap.passmap(z)
            self.assertIsNone(z, y)


if __name__ == "__main__":
    unittest.main()
