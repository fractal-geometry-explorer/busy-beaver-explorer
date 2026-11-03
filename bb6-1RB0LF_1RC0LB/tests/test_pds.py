"""Checks of the pushdown reduction (py/pds.py, c/pds.c).

usage: python3 bb6-1RB0LF_1RC0LB/tests/test_pds.py
"""
import os
import random
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, "py"))

import pds  # noqa: E402


def sim(tab, n):
    """Steps until halting, or None if the machine runs n steps."""
    t, p, s = {}, 0, 0
    for i in range(n):
        tr = tab[s][t.get(p, 0)]
        if tr is None:
            return i
        t[p] = tr[0]
        p += tr[1]
        s = tr[2]
    return None


def text_of(tab):
    return "_".join("".join("---" if t is None else f"{t[0]}{'R' if t[1] == 1 else 'L'}{chr(65 + t[2])}" for t in row)
                    for row in tab)


def proves(tab, side, nmax):
    tb = tab if side == "L" else pds.mirror(tab)
    return any(not pds.post_star(tb, d, n)[0] for n in range(1, nmax + 1) for d in pds.dfas(n))


class TestPds(unittest.TestCase):
    def test_sound_on_random_machines(self):
        """No machine that halts within 20000 steps is proved non-halting (random 2- and 3-state machines)."""
        rng = random.Random(1)
        halters = proved = 0
        for _ in range(600):
            k = rng.choice([2, 3])
            tab = [[(rng.randint(0, 1), rng.choice([1, -1]), rng.randrange(k)) for _ in (0, 1)] for _ in range(k)]
            tab[rng.randrange(k)][rng.randint(0, 1)] = None
            h = sim(tab, 20000)
            for side in "LR":
                if proves(tab, side, 3):
                    proved += 1
                    self.assertIsNone(h, (tab, side))
            halters += h is not None
        self.assertGreater(halters, 150)
        self.assertGreater(proved, 300)

    def test_known(self):
        self.assertFalse(pds.post_star(pds.parse("1RA---"), [[0, 0]], 1)[0])
        self.assertTrue(pds.post_star(pds.parse("1RB---_1LA0RA"), [[0, 0]], 1)[0])
        self.assertTrue(pds.post_star(pds.parse("1LA---"), [[0, 0]], 1)[0])       # one state is too coarse
        self.assertFalse(pds.post_star(pds.parse("1LA---"), [[0, 1], [1, 1]], 2)[0])

    def test_c_agrees(self):
        """c/pds.c finds the same DFAs as py/pds.py (up to 3 states) on random 6-state machines, and none up to 4
        states for this machine."""
        out = os.path.join(tempfile.mkdtemp(), "pds")
        subprocess.run(["gcc", "-O2", "-o", out, os.path.join(ROOT, "c", "pds.c")], check=True)
        rng = random.Random(5)
        for _ in range(25):
            tab = [[(rng.randint(0, 1), rng.choice([1, -1]), rng.randrange(6)) for _ in (0, 1)] for _ in range(6)]
            tab[rng.randrange(6)][rng.randint(0, 1)] = None
            for side in "LR":
                tb = tab if side == "L" else pds.mirror(tab)
                py = sum(1 for n in (1, 2, 3) for d in pds.dfas(n) if not pds.post_star(tb, d, n)[0])
                c = subprocess.run([out, "3", side], env=dict(os.environ, TM=text_of(tab)), check=True,
                                   capture_output=True, text=True).stdout.count("NONHALT")
                self.assertEqual(py, c, (text_of(tab), side))
        for side in "LR":
            got = subprocess.run([out, "4", side], check=True, capture_output=True, text=True).stdout
            self.assertNotIn("NONHALT", got)
            self.assertIn("n 4 tried 816", got)


if __name__ == "__main__":
    unittest.main(verbosity=2)
