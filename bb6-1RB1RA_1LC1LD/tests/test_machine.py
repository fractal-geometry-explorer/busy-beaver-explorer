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
import macro  # noqa: E402
import build_status  # noqa: E402
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

    def test_rules_lean_current(self):
        out = subprocess.run([sys.executable, os.path.join(ROOT, "lean", "rules.py")], check=True,
                             capture_output=True, text=True).stdout
        with open(os.path.join(ROOT, "lean", "Rules.lean")) as f:
            self.assertEqual(f.read(), out)

    def test_page_current(self):
        with open(os.path.join(ROOT, "status.json")) as f:
            spec = json.load(f)
        spec.setdefault("source", "bb6-1RB1RA_1LC1LD/status.json")
        with open(os.path.join(REPO, "pages", "1RB1RA_1LC1LD", "proof-status.html")) as f:
            self.assertEqual(f.read(), build_status.build(spec, spec.get("home", "../index.html")))


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



def lean_next(ls, n):
    """`next` of lean/Macro.lean, transcribed: `ls` the blocks left of the last, nearest first; `n + 1` the last."""
    x = ls[0] if ls else 0
    tl = ls[1:]
    d = tl[0] if tl else 0
    if n == 3:
        return [x + 6] + tl, 0
    if n % 6 == 3:
        return [x + 2 * ((n - 9) // 6) + 8] + tl, 4 * ((n - 9) // 6) + 4
    if n % 6 == 0 and n > 0:
        return [x + 2 * ((n - 6) // 6) + 6] + tl, 4 * ((n - 6) // 6) + 2
    if n % 6 == 1:
        return [d + 2 * (n // 6) + 2] + tl[1:], x + 4 * (n // 6) + 2
    if n % 6 == 4:
        return [d + 2 * (n // 6) + 4] + tl[1:], x + 4 * (n // 6) + 4
    return None


def one_pass(blocks, limit=10 ** 7):
    """Run from `blocks A>0` (blank around) to the next time A reads the blank cell right of the tape."""
    tp = Tape()
    pos = 0
    for i, b in enumerate(blocks):
        for _ in range(b):
            tp.set(pos, 1)
            pos += 1
        if i < len(blocks) - 1:
            pos += 1
    tp.lo, tp.hi = 0, pos
    r = Run(macro.MACHINE, state=0, tape=tp, head=pos)
    while r.steps < limit:
        if not r.step():
            return macro.HALT
        if r.state == 0 and r.head == r.tape.hi and r.tape.get(r.head) == 0:
            return macro.blocks_of(r.tape.word(r.tape.lo, r.head - 1))
    raise RuntimeError("no pass end")


class TestMacro(unittest.TestCase):
    def test_python_is_lean_next(self):
        """macro.next_pass is the `next` that lean/Macro.lean proves sound (`next_sound`)."""
        for blocks in [(5,), (3, 4), (2, 7, 9), (1, 1, 1, 2), (6, 2, 5), (8, 3, 10)]:
            for b in range(2, 40):
                got = macro.next_pass(blocks + (b,))
                ln = lean_next(list(reversed(blocks)), b - 1)
                if ln is None:
                    self.assertIsNone(got)
                    continue
                ls, n = ln
                self.assertEqual(got, tuple(reversed(ls)) + (n + 1,), (blocks, b))

    def test_any_tape(self):
        """next_pass on block lists that the run need not reach (odd blocks, blocks of 1), against direct runs."""
        import random
        rnd = random.Random(1)
        for _ in range(300):
            blocks = tuple(rnd.randint(1, 12) for _ in range(rnd.randint(1, 4))) + (rnd.randint(1, 40),)
            p = macro.next_pass(blocks)
            if p is not None:
                self.assertEqual(p, one_pass(blocks), blocks)

    def test_run(self):
        """Every pass start of the first 3*10^6 steps has single-0 separators, and next_pass agrees on all it covers."""
        agree, rec, mod3, most = macro.check(macro.pass_starts(3 * 10 ** 6))
        self.assertEqual((agree, rec, most), (81, 36, 4))

    def test_first_passes(self):
        """`blank_passes` in lean/Macro.lean: the first pass starts, and the fourth is the recursive case."""
        got = [bl for _, bl in macro.pass_starts(200)]
        self.assertEqual(got, [(2, 2), (2, 5), (4, 7), (10, 3)])
        self.assertEqual([macro.next_pass(b) for b in got], [(2, 5), (4, 7), (10, 3), None])


if __name__ == "__main__":
    unittest.main(verbosity=2)
