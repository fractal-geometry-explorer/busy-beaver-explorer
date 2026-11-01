"""py/ancestry.py: the inverse pass map, and the jumps of the return map that lean/Visit.lean is about."""
import os
import sys
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "py"))
import ancestry  # noqa: E402
import dynamics  # noqa: E402
import passmap  # noqa: E402


class TestInverse(unittest.TestCase):
    def test_inverse(self):
        """preimages(z) contains every y with passmap(y) = z (random lists), and only such y."""
        self.assertTrue(ancestry.check_inverse(3000))
        for z in ([5, 11], [14, 36, 18, 4], ancestry.HALVING["wF"]):
            for y in ancestry.preimages(z):
                self.assertEqual(passmap.passmap(y), z)

    def test_branching(self):
        """Orbit lists and the halving lists alike have many preimages: ancestry is no constraint."""
        orbit = list(passmap.orbit(1001))
        self.assertEqual(len(ancestry.preimages(orbit[1000])), 1333)
        counts = {name: len(ancestry.preimages(z)) for name, z in ancestry.HALVING.items()}
        self.assertEqual(counts, {"w7": 159, "wF": 37, "wH": 125})


class TestJumps(unittest.TestCase):
    def test_skips(self):
        """To mod 2^28: no jump skips a value = 1 mod 32, and every open class is = 1 mod 256."""
        skipped, open_ = ancestry.skips(26)
        self.assertTrue(skipped)
        self.assertTrue(all(isinstance(v, int) and v <= 4 for v in skipped))
        self.assertTrue(all(v >= 8 for v in open_))

    def test_open34(self):
        self.assertEqual(len(ancestry.open34()), 67)
        self.assertTrue(all(r % 256 == 1 for r in ancestry.open34()))

    def test_open_jumps(self):
        """Random members of the open classes jump by k <= 8 and skip no value = 1 mod 32 (sampled)."""
        ks, bad = ancestry.open_jumps(300)
        self.assertEqual(bad, 0)
        self.assertLessEqual(max(ks), 8)

    def test_orbit_visits(self):
        """Along 20,000 returns from a = 5, every a = 5 mod 12, a = 1 mod 32 below the end is visited."""
        seq, top = dynamics.orbit(20000)
        visited = {a for a, _ in seq}
        self.assertEqual([b for b in range(5, top, 12) if b % 32 == 1 and b not in visited], [])


if __name__ == "__main__":
    unittest.main()
