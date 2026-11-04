"""Checks of the pass rule (lean/Pass.lean) against the machine, and of py/passes.py against c/passes.c.

usage: python3 bb6-1RB0LF_1RC0LB/tests/test_passes.py
"""
import itertools
import os
import re
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, "py"))

import passes  # noqa: E402
from passes import B, BLANK, C, E, F, MACHINE  # noqa: E402
from bbtools.machine import Run, Tape  # noqa: E402


def run_from_C(cells):
    """Put C on cells[1] (cells[0] is the gap's first cell, behind it) and run right until the first left move or a
    halt.  Returns the state of the left move, or None for a halt."""
    tp = Tape()
    for i, c in enumerate(cells):
        tp.set(i, c)
    r = Run(MACHINE, state=C, tape=tp, head=1)
    for _ in range(10 * len(cells) + 20):
        s, y = r.state, r.tape.get(r.head)
        t = MACHINE.table[s][y]
        if t is None:
            return None
        if t[1] != 1:
            return s
        r.step()
    raise AssertionError("no end")


class TestPassRule(unittest.TestCase):
    def test_all_short_passes(self):
        """Every list of up to 6 gaps of 1 and 2, then every ending: the rule predicts who turns, or the halt."""
        n = 0
        for k in range(7):
            for gs in itertools.product([1, 2], repeat=k):
                body = [0]
                for g in gs:
                    body += [0] * (g - 1) + [1] + [0]
                body = body[:-1]  # the last gap's first cell is part of the ending below
                for end in ([0, 0, 0, 1], [0, 0, 0, 0, 1], [0] * 7 + [1], [0, 1, 1], [0, 0, 1, 1], [0, 0, 1]):
                    cells = body + end + [0, 1]
                    crossed, g = passes.ending(cells)
                    self.assertEqual(run_from_C(cells), passes.first_left(crossed, g), (gs, end))
                    n += 1
        self.assertGreater(n, 700)

    def test_gap3_halts(self):
        self.assertIsNone(run_from_C([0, 0, 0, 1, 0, 1]))
        self.assertIsNone(run_from_C([0, 1, 0, 0, 1, 0, 0, 0, 1]))  # gaps 1, 2, then 3

    def test_endings(self):
        self.assertEqual(passes.ending([0, 1, 0, 1, 0, 0, 0, 0, 1]), ([1, 1], 4))
        self.assertEqual(passes.ending([0, 0, 1, 0, 0, 0, 1]), ([2], 3))
        self.assertEqual(passes.ending([0, 1, 1]), ([1], 0))
        self.assertEqual(passes.ending([0, 0, 1, 1]), ([2], 0))
        self.assertEqual(passes.ending([0, 1, 0]), ([1], BLANK))
        self.assertEqual(passes.first_left([1], 0), B)
        self.assertEqual(passes.first_left([2], 0), F)
        self.assertEqual(passes.first_left([], 6), E)


class TestRun(unittest.TestCase):
    def test_blank_run(self):
        """From blank tape: every pass ends as predicted, none at a gap of 3, no odd run at any pass start."""
        starts, tally, mism, odd = passes.check(300000)
        self.assertEqual(mism, 0)
        self.assertEqual(odd, 0)
        self.assertEqual(tally[3], 0)
        self.assertGreater(starts, 10000)
        # pass endings: lengths 4j+2 dominate, each about half as common as the one before
        self.assertGreater(tally[6], 1.8 * tally[10])
        self.assertGreater(tally[10], 1.8 * tally[14])

    def test_c_agrees(self):
        """c/passes.c finds the same pass starts and endings as py/passes.py."""
        out = os.path.join(tempfile.mkdtemp(), "passes")
        subprocess.run(["gcc", "-O2", "-o", out, os.path.join(ROOT, "c", "passes.c")], check=True)
        steps = 300000
        got = subprocess.run([out, str(steps)], check=True, capture_output=True, text=True).stdout
        starts, tally, mism, odd = passes.check(steps)
        m = re.search(r"pass starts (\d+), odd runs (\d+)", got)
        self.assertEqual((int(m.group(1)), int(m.group(2))), (starts, odd))
        c = {}
        for line in got.splitlines():
            m = re.match(r"\s+gap (\d+): (\d+)", line)
            if m:
                c[int(m.group(1))] = int(m.group(2))
            m = re.match(r"\s+blank end: (\d+)", line)
            if m:
                c[BLANK] = int(m.group(1))
        self.assertEqual(c, dict(tally))


if __name__ == "__main__":
    unittest.main(verbosity=2)
