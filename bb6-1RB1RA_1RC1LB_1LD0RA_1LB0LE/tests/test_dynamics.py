"""py/dynamics.py: the return map's orbit is a counter, its excursions read few bits, and the deep classes mix."""
import os
import sys
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "py"))
import dynamics  # noqa: E402
import passmap  # noqa: E402
import returnmap  # noqa: E402


class TestOrbit(unittest.TestCase):
    def test_counter(self):
        """From a = 5, G adds 12k with k >= 1, and the values a = 5 mod 12 it misses are exactly those inside a
        jump; the states [a, 2a+1] of the plain pass-map orbit are the same values."""
        seq, top = dynamics.orbit(5000)
        self.assertTrue(all(k >= 1 for _, k in seq))
        s = dynamics.orbit_stats(seq, top)
        self.assertTrue(s["skipped_are_jumps"])
        self.assertLess(s["skipped"], 0.06 * s["values"])
        returns = [a for _, a in returnmap.orbit_returns(9 * 300)]
        self.assertEqual(returns[:200], [a for a, _ in seq[:200]])

    def test_deep_values_visited(self):
        """Every a = 2^r + 1 = 5 mod 12 (r even) below the end of the run is on the orbit."""
        seq, top = dynamics.orbit(20000)
        visited = {a for a, _ in seq}
        for r in range(4, top.bit_length() - 1, 2):
            self.assertIn(2 ** r + 1, visited, r)


class TestExcursion(unittest.TestCase):
    def test_against_G(self):
        for a in (5, 17, 2 ** 24 + 1, 12 * 987654321 + 5):
            k, x, m = dynamics.excursion(a)
            g, _, small = returnmap.G(a)
            self.assertEqual(g, a + 12 * k)
            self.assertAlmostEqual(x, dynamics.math.log2(a / small))

    def test_route_reads_m_bits(self):
        """Changing a above the bits the route reads changes neither the route nor k."""
        for a in (17, 2 ** 20 + 1, 12 * 31415926 + 5):
            k, _, m = dynamics.excursion(a)
            b = a + 2 ** m * 12345
            self.assertEqual(dynamics.excursion(b)[0], k)

    def test_random_size_free(self):
        """The bits read do not grow with the size of a."""
        small, big = dynamics.random_stats(64, 200), dynamics.random_stats(1024, 200)
        self.assertLess(small["m_max"], 40)
        self.assertLess(big["m_max"], 40)


class TestTree(unittest.TestCase):
    def test_tree(self):
        s = dynamics.tree(24)
        self.assertEqual((s["routes"], s["open"], s["bad"], s["points"]), (100, 20, 0, [1]))

    def test_mixing(self):
        """Every open class at depth 32 has its own coefficient vector: no repetition up to scale."""
        s = dynamics.mixing(32)
        self.assertEqual(s["shapes"], s["open"])
        self.assertEqual(s["open"], dynamics.tree(32)["open"])


if __name__ == "__main__":
    unittest.main()
