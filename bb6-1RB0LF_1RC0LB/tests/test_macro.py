"""Checks of the macro machine (lean/Macro.lean, py/macro.py) against the machine, and of py/macro.py against c/macro.c.

usage: python3 bb6-1RB0LF_1RC0LB/tests/test_macro.py
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

import macro  # noqa: E402
import twostack  # noqa: E402
import callstack  # noqa: E402
import perturb  # noqa: E402
from macro import B, F, M0, MACHINE, encode, mstep  # noqa: E402
from bbtools.machine import Run, Tape  # noqa: E402


def next_start(c):
    """Put the tape of `c` on a fresh machine and run it to the next pass start; returns (cells, head, state) as
    macro.tape_at does, or None for a halt."""
    cells, head, st = encode(c)
    tp = Tape()
    for i, x in enumerate(cells):
        tp.set(i, x)
    r = Run(MACHINE, state=st, tape=tp, head=head)
    last = 0
    for _ in range(100000):
        t = MACHINE.table[r.state][r.tape.get(r.head)]
        if t is None:
            return None
        r.step()
        last = t[1]
        if r.state in (B, F) and r.tape.get(r.head) == 0 and last == -1:
            span = range(min(r.tape.lo, 0), max(r.tape.hi, len(cells)) + 1)
            ones = [i for i in span if r.tape.get(i)]
            lo, hi = min(ones + [r.head]), max(ones + [r.head])
            return [r.tape.get(i) for i in range(lo, hi + 1)], r.head - lo, r.state
    raise AssertionError("no pass start")


def small_configs():
    """Every macro configuration with a stack of at most 2 blocks, at most 2 pairs, values up to 3."""
    vals = range(4)
    stacks = [[]] + [[a] for a in vals] + [[a, b] for a in vals for b in vals]
    words = [[]] + [[p] for p in itertools.product(vals, vals)] + \
        [[p, q] for p in itertools.product(vals, vals) for q in itertools.product(vals, vals)]
    for S in stacks[:8]:
        for ws in words:
            for mt in vals:
                yield ("F", S, ws, mt)
                for h in (1, 2, 3):
                    yield ("B", S, h, ws, mt)
        yield ("Binf", S)


class TestMacro(unittest.TestCase):
    def test_rules_on_small_configurations(self):
        """mstep agrees with the machine on every small configuration where it is defined (Lean proves it for all)."""
        n = 0
        for c in small_configs():
            d = mstep(c)
            if d is None:
                continue
            self.assertEqual(next_start(c), encode(d), c)
            n += 1
        self.assertGreater(n, 20000)

    def test_undefined_cases(self):
        """mstep gives up exactly at a gap g = 0 with an empty segment on its left, or on its right before another gap."""
        self.assertIsNone(mstep(("F", [], [(0, 0)], 3)))
        self.assertIsNone(mstep(("F", [], [(2, 0), (0, 3)], 1)))
        self.assertIsNotNone(mstep(("F", [], [(2, 0)], 0)))

    def test_run_from_blank(self):
        starts, bad, stuck = macro.check(300000)
        self.assertGreater(starts, 10000)
        self.assertEqual((bad, stuck), (0, 0))

    def test_c_agrees(self):
        with tempfile.TemporaryDirectory() as d:
            exe = os.path.join(d, "macro")
            subprocess.run(["gcc", "-O2", "-o", exe, os.path.join(ROOT, "c", "macro.c")], check=True)
            out = subprocess.run([exe, "1000000"], capture_output=True, text=True, check=True).stdout
        m = re.search(r"pass starts (\d+), mismatches (\d+), no rule (\d+)", out)
        starts, bad, stuck = macro.check(1000000)
        self.assertEqual((int(m.group(1)), int(m.group(2)), int(m.group(3))), (starts, 0, 0))
        self.assertEqual((bad, stuck), (0, 0))


class TestTwoStack(unittest.TestCase):
    def test_same_as_macro_on_small_configurations(self):
        """zstep is the F pass plus the B pass after it, stuck exactly where mstep is stuck."""
        n = 0
        for c in small_configs():
            if c[0] != "F":
                continue
            d = mstep(c)
            while d is not None and d[0] != "F":
                d = mstep(d)
            e = twostack.zstep(twostack.from_macro(c))
            self.assertEqual(e, None if d is None else twostack.from_macro(d), c)
            n += 1
        self.assertGreater(n, 5000)

    def test_run_from_blank(self):
        n, bad = twostack.check(300000)
        self.assertGreater(n, 100000)
        self.assertEqual(bad, 0)


class Counter(unittest.TestCase):
    """The counter of lean/Counter.lean on the macro machine, and the same counter on the two-stack form."""

    def check_step(self, c, d):
        p, q = callstack.mphi(c), callstack.mphi(d)
        if c[0] == "F" and d[0] == "B" and d[3]:
            self.assertEqual(q, p, c)  # phi_interior, from F
        elif c[0] == "F" and d[0] == "B":
            self.assertIn(q - p, (1, 2), c)  # phi_end
        elif c[0] == "B" and c[1]:
            self.assertEqual(q, p, c)  # phi_interior, from B
        elif c[0] == "B":
            self.assertEqual(q, p - 1, c)  # phi_bottom

    def test_small_configurations(self):
        n = 0
        for c in small_configs():
            d = mstep(c)
            if d is not None:
                self.check_step(c, d)
                n += 1
        self.assertGreater(n, 5000)

    def test_run_from_blank(self):
        c = M0
        for _ in range(200000):
            d = mstep(c)
            self.check_step(c, d)
            c = d

    def test_two_stack_interior(self):
        out = callstack.check(200000)
        for (rule, bottom, end, dphi), k in out.items():
            if not bottom and not end:
                self.assertEqual(dphi, 0)
            if rule == "R1" and end and not bottom:
                self.assertEqual(dphi, 2)


class Perturb(unittest.TestCase):
    def test_example(self):
        """py/perturb.py's example: one entry of L changed from 0 to 2 gets stuck; the run itself does not."""
        z = callstack.start()
        for _ in range(perturb.EXAMPLE_AT):
            z = twostack.zstep(z)
        e = twostack.norm([list(x) for x in perturb.EXAMPLE])
        diff = [k for k in range(len(z)) if z[k] != e[k]]
        self.assertEqual(diff, [6])
        self.assertEqual(perturb.run(e, 30000)[0], 24141)
        self.assertIsNone(perturb.run(z, 30000)[0])


if __name__ == "__main__":
    unittest.main()
