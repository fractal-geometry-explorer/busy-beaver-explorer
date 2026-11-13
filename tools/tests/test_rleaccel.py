"""Tests of bbtools.rleaccel: the accelerated run must agree exactly, tape and step count, with a direct run.

usage: python3 tools/tests/test_rleaccel.py
"""
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "py"))

from bbtools.rleaccel import Sim, parse  # noqa: E402

MACHINES = [
    "1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA",
    "1RB0LC_1LC0RE_1LD1LC_1LA1RD_1RF1RB_---0RB",
    "1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_0RA0LA",
    "1RB1RE_0LC0LF_0LA0LD_1LE1LC_1RA0LB_---0RE",
    "1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA",
]
BB5 = "1RB1LC_1RC1RB_1RD0LE_1LA1LD_---0LA"


def direct(m, nsteps):
    T = parse(m)
    tape = {}
    pos = 0
    q = 0
    for t in range(nsteps):
        tr = T[(q, tape.get(pos, 0))]
        if tr is None:
            return "halt", t + 1, tape
        tape[pos] = tr[0]
        pos += tr[1]
        q = tr[2]
    return "run", nsteps, tape


def cells(s):
    k = s.k
    out = []
    for sym, c in s.L[1:]:
        out += [int(b) for b in format(sym, "0%db" % k)] * c
    right = []
    for sym, c in s.R[1:]:
        right += [int(b) for b in format(sym, "0%db" % k)][::-1] * c
    return "".join(map(str, out + right[::-1])).strip("0")


class T(unittest.TestCase):
    def test_against_direct(self):
        jumps = 0
        for m in MACHINES:
            for k in (1, 2, 3):
                for target in (20000, 400000):
                    s = Sim(m, k)
                    s.run(10 ** 9, stop=target)
                    self.assertIsNone(s.halted)
                    self.assertIsNone(s.nonhalt)
                    kind, n, tape = direct(m, s.steps)
                    self.assertEqual(kind, "run")
                    d = "".join(str(tape.get(i, 0)) for i in range(min(tape), max(tape) + 1)).strip("0")
                    self.assertEqual(d, cells(s), (m, k, target))
                    jumps += s.njumps
        self.assertGreater(jumps, 1000)

    def test_halt(self):
        for k in (1, 2, 3):
            s = Sim(BB5, k)
            s.run(10 ** 9)
            self.assertIsNotNone(s.halted)
            self.assertEqual(s.steps, 47176870)

    def test_nonhalt(self):
        # a bouncer: one cycle rule with no shrinking count
        s = Sim("1RB1LA_1LA1RB", 1)
        s.run(10 ** 6)
        self.assertIsNotNone(s.nonhalt)


if __name__ == "__main__":
    unittest.main()
