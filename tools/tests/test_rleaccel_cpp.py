"""tools/c/rleaccel.cpp is a port of bbtools.rleaccel with the same policy: after the same number of macro steps
both must report the same machine step count and tape width, and the same halt.

usage: python3 tools/tests/test_rleaccel_cpp.py     (needs g++)
"""
import os
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "py"))

from bbtools.rleaccel import Sim  # noqa: E402

CASES = [
    ("1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA", 1, 300000),
    ("1RB0LC_1LC0RE_1LD1LC_1LA1RD_1RF1RB_---0RB", 2, 300000),
    ("1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_0RA0LA", 1, 200000),
    ("1RB1RE_0LC0LF_0LA0LD_1LE1LC_1RA0LB_---0RE", 3, 200000),
    ("1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA", 2, 200000),
]
BB5 = "1RB1LC_1RC1RB_1RD0LE_1LA1LD_---0LA"


class T(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.dir = tempfile.mkdtemp()
        cls.exe = os.path.join(cls.dir, "rleaccel")
        subprocess.check_call(["g++", "-O2", "-w", "-o", cls.exe,
                               os.path.join(os.path.dirname(HERE), "c", "rleaccel.cpp")])

    def run_cpp(self, m, k, n):
        return subprocess.check_output([self.exe, m, str(k), str(n)], text=True).strip().split("\n")

    def test_same_as_python(self):
        for m, k, n in CASES:
            s = Sim(m, k)
            s.run(n)
            out = self.run_cpp(m, k, n)
            w = out[-2].split()
            self.assertEqual((int(w[1]), int(w[3]), int(w[5])), (s.nmacro, s.steps, s.width()), m)
            self.assertEqual(out[-1], "no halt in the first %d steps" % s.steps, m)

    def test_bb5_halts(self):
        for k in (1, 2, 3):
            self.assertEqual(self.run_cpp(BB5, k, 10 ** 8)[-1], "HALTED after 47176870 steps")


if __name__ == "__main__":
    unittest.main()
