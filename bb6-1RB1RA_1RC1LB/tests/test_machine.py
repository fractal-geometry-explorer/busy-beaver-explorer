"""Checks on this machine's generated files and simulators (run with tools/tests/test_tools.py in CI).

usage: python3 bb6-1RB1RA_1RC1LB/tests/test_machine.py
"""
import os
import subprocess
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
TOOLS = os.path.join(os.path.dirname(ROOT), "tools")
sys.path.insert(0, os.path.join(TOOLS, "py"))

from bbtools.leangen import machine_lean  # noqa: E402
from bbtools.machine import Machine, Run, Tape  # noqa: E402

sys.path.insert(0, os.path.join(ROOT, "py"))
import macro  # noqa: E402

M = "1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB"


class TestGenerated(unittest.TestCase):
    def test_machine_lean_current(self):
        with open(os.path.join(ROOT, "lean", "Machine.lean")) as f:
            src = f.read()
        self.assertIn(f'def text : String := "{M}"', src)
        doc = "The six-state machine this folder studies; whether it halts from blank tape is open."
        self.assertEqual(src, machine_lean(M, "BB6b", doc))

    def test_rules_lean_current(self):
        out = subprocess.run([sys.executable, os.path.join(ROOT, "lean", "rules.py")], check=True,
                             capture_output=True, text=True).stdout
        with open(os.path.join(ROOT, "lean", "Rules.lean")) as f:
            self.assertEqual(f.read(), out)

    def test_page_current(self):
        sys.path.insert(0, os.path.join(TOOLS, "pages"))
        import json
        import build_status
        with open(os.path.join(ROOT, "status.json")) as f:
            spec = json.load(f)
        spec.setdefault("source", "bb6-1RB1RA_1RC1LB/status.json")
        with open(os.path.join(os.path.dirname(ROOT), "pages", "1RB1RA_1RC1LB", "proof-status.html")) as f:
            self.assertEqual(f.read(), build_status.build(spec, spec.get("home", "../index.html")))


class TestRun(unittest.TestCase):
    def test_no_halt_early(self):
        r = Run(Machine.parse(M))
        self.assertFalse(r.run(200000))

    def test_first_left_returns(self):
        """The first returns of the head to the left end in state F (notes/LAB_NOTES.md)."""
        r = Run(Machine.parse(M))
        seen = []
        while r.steps < 20000:
            r.step()
            if r.state == 5 and r.head == r.tape.lo:
                seen.append(r.steps)
        self.assertEqual(seen, [5, 81, 1135])


def tape_cells(r):
    """The marked cells of a run from the first 1 to the last, and the head's index among them."""
    ones = [p for p in range(r.tape.lo - 2, r.tape.hi + 3) if r.tape.get(p)]
    lo, hi = ones[0], ones[-1]
    return [r.tape.get(p) for p in range(lo, hi + 1)], r.head - lo


class TestMacro(unittest.TestCase):
    """py/macro.py, the map that lean/Macro.lean proves sound, against the reference simulator."""

    def test_matches_simulation(self):
        """Every macro configuration of the first 1000 macro steps, at the step count the model gives."""
        r = Run(Machine.parse(M))
        for m, t, ls, n, cs in macro.run(1000):
            self.assertFalse(r.run(t))
            self.assertEqual(r.steps, t)
            self.assertEqual(r.state, 0, m)
            self.assertEqual(tape_cells(r), macro.tape(ls, n, cs), m)

    def test_step_count(self):
        """The same number as `runM_1000` in lean/MacroRun.lean."""
        *_, last = macro.run(1000)
        self.assertEqual(last[1], 1322171)

    def test_halting_branch(self):
        """From X(ls, n, cs) with n odd and every left block 2 after the transfers, the machine halts where the model
        says; with one block changed it does not."""
        for ls, n, cs in [([2], 1, []), ([1], 3, [4]), ([2, 2, 2], 1, [1, 3]), ([1, 2], 3, [])]:
            res = macro.next_step(ls, n, cs)
            self.assertEqual(res[0], 'halt')
            cells, h = macro.tape(ls, n, cs)
            tp = Tape()
            for i, v in enumerate(cells):
                tp.set(i - h, v)
            r = Run(Machine.parse(M), state=0, tape=tp, head=0)
            self.assertTrue(r.run(10 ** 6))
            self.assertEqual(r.steps, res[1] + 1)
        self.assertEqual(macro.next_step([2, 3], 1, [])[0], 'go')


if __name__ == "__main__":
    unittest.main(verbosity=2)
