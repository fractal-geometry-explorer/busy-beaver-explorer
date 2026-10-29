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
from bbtools.machine import Machine, Run  # noqa: E402

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


if __name__ == "__main__":
    unittest.main(verbosity=2)
