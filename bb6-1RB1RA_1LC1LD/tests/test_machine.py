"""Checks on this machine's generated files and its run from blank tape (CI runs them, .github/workflows/tests.yml).

usage: python3 bb6-1RB1RA_1LC1LD/tests/test_machine.py
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
import build_status  # noqa: E402
from bbtools import ctl  # noqa: E402
from bbtools.invariants import conserved  # noqa: E402
from bbtools.leangen import machine_lean  # noqa: E402
from bbtools.machine import Machine, Run, Tape, records  # noqa: E402

M = "1RB1RA_1LC1LD_1LD0LB_1RE0RF_---1RD_1RA1RB"


class TestGenerated(unittest.TestCase):
    def test_machine_lean_current(self):
        with open(os.path.join(ROOT, "lean", "Machine.lean")) as f:
            src = f.read()
        doc = "The six-state machine this folder studies; whether it halts from blank tape is open."
        self.assertEqual(src, machine_lean(M, "BB6c", doc))

    def test_page_current(self):
        with open(os.path.join(ROOT, "status.json")) as f:
            spec = json.load(f)
        spec.setdefault("source", "bb6-1RB1RA_1LC1LD/status.json")
        with open(os.path.join(REPO, "pages", "1RB1RA_1LC1LD", "proof-status.html")) as f:
            self.assertEqual(f.read(), build_status.build(spec, spec.get("home", "../index.html")))


    def test_edge_cert_current(self):
        with open(os.path.join(ROOT, "lean", "EdgeCert.lean")) as f:
            self.assertEqual(f.read(), ctl.lean_file(M, 3, "BB6c"))


class TestEdge(unittest.TestCase):
    """The closed tape language of lean/EdgeCert.lean and what lean/Edge.lean draws from it."""

    @classmethod
    def setUpClass(cls):
        cls.AL, cls.AR, cls.S = ctl.search(M, 3)

    def test_closed(self):
        self.assertTrue(ctl.check(M, self.AL, self.AR, self.S))
        self.assertTrue(ctl.no_double_zero(self.AR, self.S))
        B = set(self.AR.blank_only())
        halts = ctl.halting(M, self.AR, self.S)
        self.assertTrue(halts)
        for (s, ql, qr, x, qr2) in halts:
            self.assertEqual((s, x, ctl.show(self.AL.windows[ql])), (4, 0, "111"))
            self.assertIn(qr2, B)

    def test_covers_run(self):
        """Every configuration of the first 20,000 steps is in the set."""
        r = Run(blank.MACHINE)
        while r.steps < 20000:
            t, h = r.tape, r.head
            left = [t.get(p) for p in range(h - 1, t.lo - 1, -1)]
            right = [t.get(p) for p in range(h, t.hi + 1)]
            self.assertIn(ctl.abstract(self.AL, self.AR, r.state, left, right), self.S, r.steps)
            r.step()

    def test_right_no_double_zero(self):
        """`right_no_double_zero` on the run: past the head cell, no 0 0 before the blank region (sampled)."""
        r = Run(blank.MACHINE)
        while r.steps < 10 ** 6:
            for _ in range(997):
                r.step()
            right = "".join(str(r.tape.get(p)) for p in range(r.head + 1, r.tape.hi + 2)).rstrip("0")
            self.assertNotIn("00", right, r.steps)


class TestRun(unittest.TestCase):
    def test_machine(self):
        self.assertEqual(blank.MACHINE.halting_transitions(), ["E0"])

    def test_no_halt_early(self):
        self.assertEqual(blank.summary(10 ** 6), (False, 10 ** 6, 273, 288))

    def test_step_46(self):
        """The configuration of `blank_at_46` in lean/Blank.lean."""
        r = Run(blank.MACHINE)
        r.run(46)
        self.assertEqual(r.config_str(), "1^2 0 1^5 A>0")

    def test_first_left_d(self):
        """The first times D reads the leftmost visited cell (notes/LAB_NOTES.md)."""
        seen = [(r.steps, r.config_str()) for r in blank.d_left(100)]
        self.assertEqual(seen, [(5, "D>0 1^2 0 1"), (29, "D>1 1^2 0 1^3"), (38, "D>0 1^2 0 1^4"),
                                (72, "D>1 1^2 0 1^3 0 1^2"), (81, "D>0 1^2 0 1^4 0 1^2")])

    def test_halt_shape(self):
        """`halt_shape`: D>0 0 halts on its second step, with the halting transition counted (bbchallenge)."""
        tp = Tape()
        tp.set(-1, 1)
        tp.set(2, 1)
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
