"""Checks on this machine's generated files and its run from blank tape (CI runs them, .github/workflows/tests.yml).

usage: python3 bb6-1RB0LF_1RC0LB/tests/test_machine.py
"""
import json
import os
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
REPO = os.path.dirname(ROOT)
TOOLS = os.path.join(REPO, "tools")
sys.path.insert(0, os.path.join(TOOLS, "py"))
sys.path.insert(0, os.path.join(TOOLS, "pages"))
sys.path.insert(0, os.path.join(ROOT, "py"))

import blank  # noqa: E402
import build_explainer  # noqa: E402
import build_status  # noqa: E402
from bbtools.invariants import conserved  # noqa: E402
from bbtools.leangen import machine_lean  # noqa: E402
from bbtools.machine import Machine, Run, Tape, records  # noqa: E402

M = "1RB0LF_1RC0LB_1RD1RB_1RE1RF_1LA---_0RC1LA"
PAGES = os.path.join(REPO, "pages", "1RB0LF_1RC0LB")


def spec():
    with open(os.path.join(ROOT, "status.json")) as f:
        s = json.load(f)
    s.setdefault("source", "bb6-1RB0LF_1RC0LB/status.json")
    return s


class TestGenerated(unittest.TestCase):
    def test_machine_lean_current(self):
        with open(os.path.join(ROOT, "lean", "Machine.lean")) as f:
            src = f.read()
        doc = "The six-state machine this folder studies; whether it halts from blank tape is open."
        self.assertEqual(src, machine_lean(M, "BB6e", doc))

    def test_status_page_current(self):
        s = spec()
        with open(os.path.join(PAGES, "proof-status.html")) as f:
            self.assertEqual(f.read(), build_status.build(s, s.get("home", "../index.html")))

    def test_explainer_current(self):
        s = spec()
        with open(os.path.join(PAGES, "explainer.html")) as f:
            self.assertEqual(f.read(), build_explainer.build(s, s.get("home", "../index.html")))


class TestRun(unittest.TestCase):
    def test_machine(self):
        self.assertEqual(blank.MACHINE.halting_transitions(), ["E1"])

    def test_no_halt_early(self):
        self.assertEqual(blank.summary(10 ** 6), (False, 10 ** 6, 105, 199))

    def test_step_63(self):
        """The configuration of `blank_at_63` in lean/Blank.lean."""
        r = Run(blank.MACHINE)
        r.run(63)
        self.assertEqual(r.config_str(), "0 1^2 0 1^4 C>0")

    def test_first_d_zero(self):
        """The first times D reads a 0 (notes/LAB_NOTES.md): the cell to its right is a 0 each time."""
        seen = [(r.steps, r.config_str()) for r in blank.d_zero(100)]
        self.assertEqual(seen, [(3, "1^3 D>0"), (14, "1^2 D>0 0 1 0 1"), (28, "0 1^4 D>0 0 1"),
                                (48, "0 1^4 D>0 0^2"), (64, "0 1^2 0 1^5 D>0"), (79, "1^2 D>0 0^3 1 0 1 0 1"),
                                (98, "0 1^2 0 1^4 0 1^5 D>0")])

    def test_d_zero_right(self):
        """In the first 300,000 steps D never reads a 0 with a 1 to its right, which would halt."""
        n = 0
        for r in blank.d_zero(300000):
            self.assertEqual(r.tape.get(r.head + 1), 0, r.steps)
            n += 1
        self.assertGreater(n, 10000)

    def test_halt_shape(self):
        """`halt_shape`: D>0 1 halts on its second step, with the halting transition counted (bbchallenge)."""
        tp = Tape()
        tp.set(1, 1)
        r = Run(blank.MACHINE, state=3, tape=tp, head=0)
        self.assertTrue(r.run(10))
        self.assertEqual(r.steps, 2)

    def test_no_small_invariant(self):
        """No conserved a*ones + b*pos + W[state] modulo 2 to 8 (tools/py/bbtools/invariants.py)."""
        for mod in range(2, 9):
            self.assertEqual(conserved(blank.MACHINE, mod), [], mod)

    def test_c_agrees(self):
        """tools/c/tmrun gives the same records as the Python simulator."""
        out = os.path.join(tempfile.mkdtemp(), "tmrun")
        subprocess.run(["gcc", "-O2", "-o", out, os.path.join(TOOLS, "c", "tmrun.c")], check=True)
        got = subprocess.run([out, M, "100000", "records", "80"],
                             check=True, capture_output=True, text=True).stdout.splitlines()
        py = [f"{t} {side} {r.tape.hi - r.tape.lo} {r.config_str()}" for t, side, r in records(Machine.parse(M), 100000)]
        self.assertEqual(got[:-1], py[:80])
        self.assertEqual(got[-1], "running 100000 " + str(blank.summary(100000)[2]))


if __name__ == "__main__":
    unittest.main(verbosity=2)
