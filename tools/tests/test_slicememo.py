"""tools/c/slicememo.cpp (memoized slice-stack engine) against direct simulation: the BB5 champion's step count,
the exact halting step count of 1RB0RD_1RC0LF_0LA0RB_1RE---_1LB1RA_0LE0LF (DeepMind's halt, about 8.9e27 steps),
and tapes at fixed steps of two machines equal to tools/c/tapeat.c's.

usage: python3 tools/tests/test_slicememo.py     (needs g++ and gcc)
"""
import os
import subprocess
import tempfile
import unittest

C = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "c")
BB5 = "1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA"
M88 = "1RB0RD_1RC0LF_0LA0RB_1RE---_1LB1RA_0LE0LF"
M91 = "1RB1LD_1LC0RF_0RD0LB_1LB0LE_1LA---_0RA0RF"


class T(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        d = tempfile.mkdtemp()
        cls.sm = os.path.join(d, "slicememo")
        cls.tapeat = os.path.join(d, "tapeat")
        subprocess.check_call(["g++", "-O2", "-w", "-DEXACT", "-o", cls.sm, os.path.join(C, "slicememo.cpp")])
        subprocess.check_call(["gcc", "-O2", "-o", cls.tapeat, os.path.join(C, "tapeat.c")])

    def run_sm(self, args, stopat=None):
        env = dict(os.environ)
        if stopat:
            env["STOPAT"] = str(stopat)
        out = subprocess.run([self.sm] + args, capture_output=True, text=True, env=env, timeout=600).stdout
        return out.strip().split("\n")

    def field(self, line, key):
        return [w for w in line.split() if w.startswith(key + "=")][0].split("=", 1)[1]

    def test_bb5(self):
        last = self.run_sm([BB5, "1000", "N", "fix16", "100000000"])[-1]
        self.assertIn(" HALT ", last)
        self.assertEqual(self.field(last, "steps"), "47176870")

    def test_88_halts(self):
        last = self.run_sm([M88, "3000000", "L", "fix16", "300000000"])[-1]
        self.assertIn(" HALT ", last)
        self.assertEqual(self.field(last, "steps"), "8858384066696346875382727786")

    def test_snapshots(self):
        for m, args, n in [(M88, ["3000000", "L", "fix16", "300000000"], 20597098),
                           (M91, ["3000000", "R", "fix32", "50000000"], 20210287)]:
            snap = [x for x in self.run_sm([m] + args, stopat=n) if x.startswith("SNAP")]
            want = subprocess.check_output([self.tapeat, m, str(n)], text=True).strip()
            self.assertEqual(snap, [want], m)


if __name__ == "__main__":
    unittest.main()
