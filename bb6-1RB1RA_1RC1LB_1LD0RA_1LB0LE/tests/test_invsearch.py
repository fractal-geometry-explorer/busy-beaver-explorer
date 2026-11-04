"""Tests of py/invsearch.py: the case maps, the invariant psi, the linear facts found inductive, the free-parity game,
and the (block count, psi, stop) graphs (CI runs them, .github/workflows/tests.yml).

usage: python3 bb6-1RB1RA_1RC1LB_1LD0RA_1LB0LE/tests/test_invsearch.py
"""
import itertools
import os
import random
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, "py"))

import invsearch as I  # noqa: E402
import passmap  # noqa: E402


def small_lists(kmax, bmax):
    for k in range(1, kmax + 1):
        for y in itertools.product(range(1, bmax + 1), repeat=k):
            yield list(y)


class TestCases(unittest.TestCase):
    def test_image_is_passmap(self):
        """`image` (the closed form case by case) agrees with passmap.passmap wherever it applies."""
        rnd = random.Random(1)
        for _ in range(20000):
            y = [rnd.randint(1, 40) for _ in range(rnd.randint(1, 7))]
            j = passmap.stop_index(y)
            z = passmap.passmap(y)
            if j and z is not None:
                self.assertEqual(I.image(y, j), z, y)
                self.assertEqual(len(z), I.new_length(len(y), j), y)

    def test_linear_part_keeps_the_sum(self):
        rnd = random.Random(2)
        for _ in range(2000):
            y = [rnd.random() for _ in range(rnd.randint(2, 7))]
            for j in range(1, len(y) + 1):
                self.assertAlmostEqual(sum(I.linear_image(y, j)), sum(y))


class TestPsi(unittest.TestCase):
    def test_psi_step_every_small_list(self):
        """2 psi(next y) = -psi(y) + 3(-2)^n - 7, n = k - j: every list of up to 5 blocks of size up to 9, and of 6
        blocks of size up to 5."""
        n = 0
        for y in itertools.chain(small_lists(5, 9), (list(t) for t in itertools.product(range(1, 6), repeat=6))):
            z = passmap.passmap(y)
            if isinstance(z, list):
                k, j = len(y), passmap.stop_index(y)
                self.assertEqual(2 * I.psi(z), -I.psi(y) + I.psi_const(k - j), y)
                self.assertEqual(I.psi(z), I.psi_step(I.psi(y), k - j))
                n += 1
        self.assertGreater(n, 60000)

    def test_psi_step_random_long_lists(self):
        rnd = random.Random(3)
        for _ in range(5000):
            y = [rnd.randint(2, 10 ** 6) for _ in range(rnd.randint(2, 14))]
            z = passmap.passmap(y)
            if isinstance(z, list):
                self.assertEqual(I.psi(z), I.psi_step(I.psi(y), len(y) - passmap.stop_index(y)), y)

    def test_psi_facts(self):
        """psi of [a, 2a+d] is d; the last block's parity is psi mod 2; the fold form."""
        for a in range(1, 30):
            for d in range(-3, 4):
                self.assertEqual(I.psi([a, 2 * a + d]), d)
        rnd = random.Random(4)
        for _ in range(1000):
            y = [rnd.randint(1, 99) for _ in range(rnd.randint(1, 8))]
            self.assertEqual(I.psi(y) % 2, y[-1] % 2)
            self.assertEqual(I.psi(y), sum((-2) ** (len(y) - 1 - i) * v for i, v in enumerate(y)))

    def test_the_loop_of_110_63_23(self):
        """[110, 63, 23] meets the event by the halving loop (front stop on 3 blocks, even last on 4), and along the
        loop psi goes to (psi - 13)/4: -175, -47, -15, -7, -5."""
        out, end = I.loop_psi([110, 63, 23])
        self.assertIsNone(end)
        threes = [p for y, p, j in out if len(y) == 3 and j == 1]
        self.assertEqual(threes, [-175, -47, -15, -7, -5])
        for a, b in zip(threes, threes[1:]):
            self.assertEqual(b, (a - 13) // 4)

    def test_loop_dies_for_any_psi(self):
        """The loop needs psi = 1 mod 4 at every round, and psi -> (psi - 13)/4 contracts to -13/3: from any |psi| <=
        10^6 it runs at most log4(|psi| + 5) + 2 rounds."""
        import math
        for p0 in range(-10 ** 4, 10 ** 4 + 1):
            p, r = p0, 0
            while p % 4 == 1:
                p, r = (p - 13) // 4, r + 1
            self.assertLessEqual(r, math.log(abs(p0) + 5, 4) + 2, p0)

    def test_orbit_psi_bounded(self):
        """On the first 2*10^5 passes (block count, psi, stop index) stays among the triples of the 10^8-pass run,
        which are among those of every excursion class to mod 2^66; at most 6 blocks."""
        orbit = I.read_triples(os.path.join(ROOT, "runs", "psi_triples_orbit.txt"))
        classes = I.read_triples(os.path.join(ROOT, "runs", "psi_triples_classes.txt"))
        self.assertTrue(set(orbit) <= set(classes))
        self.assertEqual((len(orbit), len(classes)), (65, 82))
        T = I.orbit_triples(200000)
        self.assertTrue(set(T) <= set(orbit))
        self.assertLessEqual(max(k for k, _, _ in classes), 6)

    def test_class_triples_small_depth(self):
        """class_triples at depth 16 lies inside the stored deeper set."""
        classes = I.read_triples(os.path.join(ROOT, "runs", "psi_triples_classes.txt"))
        self.assertTrue(set(I.class_triples(16)) <= set(classes))


class TestLinearFacts(unittest.TestCase):
    def test_houdini_facts_closed(self):
        """y2 >= y1 + 2 and S >= 2 y1 + 2 (the core of the Houdini conjunction) are kept by every pass, on every Good
        list with 4 | ones of up to 4 blocks of size up to 16 and 5 blocks of size up to 9."""
        P = lambda y: (len(y) < 2 or y[1] >= y[0] + 2) and sum(y) >= 2 * y[0] + 2  # noqa: E731
        for K, B in ((4, 16), (5, 9)):
            r = I.exhaustive_closed(P, K, B)
            self.assertTrue(r is None or r[1] is None, r)   # only stop blocks of 1 escape, never a broken fact

    def test_ratio_facts_not_closed(self):
        """y1 >= S/64 is not kept: [3, 61] -> [1, 35, 32]."""
        self.assertEqual(passmap.passmap([3, 61]), [1, 35, 32])


class TestGames(unittest.TestCase):
    def test_free_parity_game_collapses(self):
        b = I.free_parity_game(14)
        self.assertLess(b[-1], 0.001)
        b2 = I.free_parity_game(14, forbid=I.two_front)
        self.assertLess(b2[-1], 0.005)

    def test_parity_graphs(self):
        """With psi, no two front stops in a row, and at most 4 (5) blocks, front-stop runs are at most 2 (5) and the
        shape game keeps the first block above 0.08 (0.002) of the ones."""
        G4 = I.parity_graph(4)
        self.assertEqual(I.run_bound(G4), 2)
        least, _, _, conv = I.shape_game(G4, ((2, 1, False), I.START_SHAPE))
        self.assertTrue(conv)
        self.assertGreater(least, 0.08)
        G5 = I.parity_graph(5)
        self.assertEqual(I.run_bound(G5), 5)
        least, _, _, conv = I.shape_game(G5, ((2, 1, False), I.START_SHAPE), grid=1e-2)
        self.assertTrue(conv)
        self.assertGreater(least, 0.002)

    def test_orbit_graph(self):
        G = I.graph_of(I.read_triples(os.path.join(ROOT, "runs", "psi_triples_orbit.txt")))
        self.assertEqual(I.run_bound(G), 7)


if __name__ == "__main__":
    unittest.main()
