"""Checks on this machine's generated files, its pages and the observations of notes/LAB_NOTES.md (CI runs them,
.github/workflows/tests.yml).

usage: python3 bb6-1RB1RF_1LC0LB/tests/test_machine.py        (a few seconds)
"""
import json
import os
import subprocess
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
REPO = os.path.dirname(ROOT)
TOOLS = os.path.join(REPO, "tools")
sys.path.insert(0, os.path.join(TOOLS, "py"))
sys.path.insert(0, os.path.join(TOOLS, "pages"))
sys.path.insert(0, os.path.join(ROOT, "py"))

import blank  # noqa: E402
import replay  # noqa: E402
import build_status  # noqa: E402
from bbtools.invariants import conserved  # noqa: E402
from bbtools.leangen import machine_lean  # noqa: E402
from bbtools.machine import Run  # noqa: E402

M = "1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE---"
LEFT = os.path.join(ROOT, "runs", "left_1e10.txt")


class TestGenerated(unittest.TestCase):
    def test_machine_lean_current(self):
        with open(os.path.join(ROOT, "lean", "Machine.lean")) as f:
            src = f.read()
        doc = "The six-state machine this folder studies; whether it halts from blank tape is open."
        self.assertEqual(src, machine_lean(M, "BB6e", doc))

    def test_rules_lean_current(self):
        out = subprocess.run([sys.executable, os.path.join(ROOT, "lean", "rules.py")], check=True,
                             capture_output=True, text=True).stdout
        with open(os.path.join(ROOT, "lean", "Rules.lean")) as f:
            self.assertEqual(f.read(), out)

    def test_page_current(self):
        with open(os.path.join(ROOT, "status.json")) as f:
            spec = json.load(f)
        spec.setdefault("source", "bb6-1RB1RF_1LC0LB/status.json")
        with open(os.path.join(REPO, "pages", "1RB1RF_1LC0LB", "proof-status.html")) as f:
            self.assertEqual(f.read(), build_status.build(spec, spec.get("home", "../index.html")))


class TestRun(unittest.TestCase):
    def test_machine(self):
        self.assertEqual(blank.MACHINE.halting_transitions(), ["F1"])

    def test_no_halt_early(self):
        self.assertEqual(blank.summary(10 ** 6), (False, 10 ** 6, 1188, 2377))

    def test_halting_shape_on_run(self):
        """`d_right_zero` and `a_entry` on the run: D always has a 0 to its right, A always comes from E on a 0."""
        r = Run(blank.MACHINE)
        prev = None
        while r.steps < 200000:
            if r.state == blank.D:
                self.assertEqual(r.tape.get(r.head + 1), 0, r.steps)
            if r.state == blank.A and prev is not None:
                self.assertEqual(prev, (blank.E, 0), r.steps)
            prev = (r.state, r.tape.get(r.head))
            self.assertTrue(r.step())

    def test_left_events_match_c(self):
        """py/blank.py left gives the first lines of runs/left_1e10.txt (written by tools/c/tokrun)."""
        with open(LEFT) as f:
            c_lines = [line.rstrip("\n") for line in f][:24]
        py = [f"{t} L {w} {s} {ws}" for t, w, s, ws in blank.left_events(3 * 10 ** 6)][:24]
        self.assertEqual(py, c_lines)

    def test_growth_file(self):
        with open(os.path.join(ROOT, "runs", "growth_1e10.txt")) as f:
            rows = [list(map(int, line.split())) for line in f]
        self.assertEqual(rows[-1], [10 ** 10, 258671, 129335, 207])
        for t, w, ones, _ in rows[:13]:     # up to 10^5 steps
            h, t2, o2, w2 = blank.summary(t)
            self.assertEqual((h, t2, o2, w2), (False, t, ones, w))

    def test_no_invariant(self):
        """No conserved a*ones + b*pos + W[state] modulo 2 to 8 (tools/py/bbtools/invariants.py)."""
        for mod in range(2, 9):
            self.assertEqual(conserved(blank.MACHINE, mod), [], mod)


class TestObservations(unittest.TestCase):
    def test_blocks(self):
        self.assertEqual(blank.blocks("0^2 a^13 0 a^13 0 a^18 1"), [13, 13, 18])
        self.assertEqual(blank.blocks("0^2 a 0 a^7 0 a^8 1"), [1, 7, 8])
        self.assertIsNone(blank.blocks("0^2 a^3 0^2 a^9 0 a^12 1"))

    def test_marks_follow_pairs(self):
        """At every left-end moment to 10^10 steps, the word b = 110 comes right after a block of pairs."""
        n = 0
        with open(LEFT) as f:
            for line in f:
                t = line.split()[4:]
                for i, w in enumerate(t):
                    if w == "b" or w.startswith("b^"):
                        n += 1
                        self.assertTrue(i > 0 and t[i - 1].startswith("a"), line)
        self.assertEqual(n, 67)

    def test_replay(self):
        ws = {(t, w): (n, rest) for t, j, w, n, rest in replay.walls(replay.read_events(LEFT)) if n >= 2}
        self.assertEqual(len(ws), 10)
        n, rest = ws[(277787, 257)]
        self.assertEqual(n, 29)
        lost = [257 - x for x in rest]
        self.assertEqual(lost[:8], [1, 4, 6, 10, 12, 22, 28, 38])
        # every wall loses the same amounts
        for (t, w), (n, rest) in ws.items():
            self.assertEqual([w - x for x in rest], lost[:n], t)


if __name__ == "__main__":
    unittest.main(verbosity=2)
