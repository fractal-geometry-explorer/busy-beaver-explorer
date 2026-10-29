"""Checks of the block-list macro (py/waves.py) and its C version (c/blkrun.c) against direct simulation.

usage: python3 bb6-1RB1RA_1RC1LB/tests/test_waves.py        (about 15 s)
"""
import os
import re
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
TOOLS = os.path.join(os.path.dirname(ROOT), "tools")
sys.path.insert(0, os.path.join(TOOLS, "py"))
sys.path.insert(0, os.path.join(ROOT, "py"))

from bbtools.machine import Machine, Run  # noqa: E402
import waves  # noqa: E402

BUILD = tempfile.mkdtemp(prefix="waves-test-")


def cc(src, name):
    out = os.path.join(BUILD, name)
    if not os.path.exists(out):
        subprocess.run(["gcc", "-O2", "-Wall", "-Wextra", "-Werror", "-o", out, src], check=True)
    return out


def blocks_of(tape):
    """'1 0 1^4 0 1^3 0 1 A>0' (the head last) -> [1, 4, 3, 1]."""
    runs = []
    for tok in tape.split()[:-1]:
        v, _, k = tok.partition("^")
        runs.append((v, int(k or 1)))
    while runs and runs[0][0] == "0":
        runs.pop(0)
    out = [0]
    for v, k in runs:
        if v == "1":
            out[-1] += k
        else:
            assert k == 1, tape
            out.append(0)
    return out


class TestAgainstDirect(unittest.TestCase):
    def test_events_tmrun(self):
        """Every event (A at the right end) of the first 10^9 steps: the block lists and the step counts."""
        tmrun = cc(os.path.join(TOOLS, "c", "tmrun.c"), "tmrun")
        out = subprocess.run([tmrun, waves.M, str(10 ** 9), "records", str(10 ** 6)], check=True,
                             capture_output=True, text=True).stdout.splitlines()
        self.assertTrue(out[-1].startswith("running"))
        direct = [(int(s), blocks_of(t)) for s, side, _, t in (line.split(" ", 3) for line in out[:-1])
                  if side == "R" and t.endswith("A>0")]
        self.assertEqual(len(direct), 12927)
        for got, want in zip(waves.events(len(direct)), direct):
            self.assertEqual((got[1], got[2]), want)

    def test_events_reference(self):
        """The same against the Python reference simulator, for the first 300,000 steps."""
        r = Run(Machine.parse(waves.M))
        ev = waves.events(10 ** 6)
        while r.steps < 300000:
            hi = r.tape.hi
            r.step()
            if r.state == 0 and r.tape.hi > hi:
                cells = "".join(map(str, r.tape.word(r.tape.lo, r.tape.hi - 1))).lstrip("0")
                _, t, b = next(ev)
                self.assertEqual((r.steps, [len(x) for x in cells.split("0")]), (t, b))

    def test_left_records(self):
        """The new cells on the left up to 10^10 steps (runs/left_records_1e10.txt): each B record is the wave
        arriving there, each F record follows a wave arriving with c = 2 by 13 steps (the y = 1 end), and the first,
        at step 5, comes before the first event."""
        with open(os.path.join(ROOT, "runs", "left_records_1e10.txt")) as f:
            rec = [(int(x.split()[0]), x.split()[3][0]) for x in f if " L " in x]
        arr = waves.left_arrivals(56000)          # up to about 2.3 10^10 steps
        want = [(5, "F")]
        for _, t, c in arr:
            want.append((t, "B"))
            if c == 2:
                want.append((t + 13, "F"))
        self.assertEqual(sorted(want), rec)

    def test_next_left_return(self):
        """The next arrival at the left end, predicted by the macro beyond the 10^10 steps simulated so far, and
        checked by a direct run of 2.7 10^10 steps (about 2.5 minutes; set WAVES_LONG=1 to run it)."""
        arr = waves.left_arrivals(60000)
        self.assertEqual(arr[12], (56718, 26618972322, 110037))
        if os.environ.get("WAVES_LONG"):
            src = os.path.join(BUILD, "leftrec.c")
            with open(src, "w") as f:
                f.write('#include "tm.h"\nint main(int c, char **v) { (void)c; tm_machine m; tm_parse(v[1], &m);\n'
                        ' tm_tape t; tm_tape_init(&t, 1 << 20); int st = 0; long long k = 0, max = atoll(v[2]);\n'
                        ' while (k < max) { long long lo = t.lo; k++; if (!tm_step(&m, &t, &st)) return 1;\n'
                        '  if (t.lo < lo) printf("%lld\\n", k); } return 0; }\n')
            exe = os.path.join(BUILD, "leftrec")
            subprocess.run(["gcc", "-O2", "-I", os.path.join(TOOLS, "c"), "-o", exe, src], check=True)
            out = subprocess.run([exe, waves.M, "27000000000"], check=True, capture_output=True, text=True).stdout
            self.assertEqual(int(out.split()[-1]), 26618972322)

    def test_halt_branch(self):
        """The halting branch, on a tape the run itself does not reach: 1^5 A>0 sends a wave to the left end with
        c = 4 -> 0, and the machine halts after the predicted number of steps."""
        with self.assertRaises(waves.Halt) as e:
            waves.step([5])
        r = Run(Machine.parse(waves.M))
        for p in range(5):
            r.tape.set(p - 5, 1)
        n = 0
        while r.step():
            n += 1
        self.assertEqual(n + 1, e.exception.args[0])


class TestSuperstep(unittest.TestCase):
    def test_superstep_is_four_macro_steps(self):
        b = list(waves.START)
        for _ in range(3):
            b, _ = waves.step(b)
        self.assertEqual(b, [1, 6, 5, 0])
        P, kinds = b[:-2], set()
        for _ in range(150000):
            for _ in range(4):
                b, _ = waves.step(b)
            P2, kind, v = waves.superstep(P)
            kinds.add(kind)
            self.assertEqual(b, P2 + [5, 0])
            n = waves.big_n(P)
            v2 = (n & -n).bit_length() - 1
            if kind == "turn":
                self.assertEqual(v, v2 + 1)
            else:
                self.assertGreaterEqual(v2, len(P) - 1)
                self.assertEqual(v, n >> (len(P) - 1))
            P = P2
        self.assertEqual(kinds, {"turn", "left", "F"})

    def test_superstep_halt(self):
        """d_1 a power of two is the halt: P = (6) has d_1 = 6 + 20/2 = 16, and the macro halts on [6, 5, 0]."""
        P2, kind, v = waves.superstep([6])
        self.assertEqual((P2, kind, v), (None, "halt", 16))
        with self.assertRaises(waves.Halt):
            b = [6, 5, 0]
            for _ in range(4):
                b, _ = waves.step(b)


class TestAgainstMacro(unittest.TestCase):
    def test_macro_configurations_lead_to_events(self):
        """The other cut of the run (py/macro.py, proved in lean/Macro.lean): from each of its first 2,000
        configurations, direct simulation reaches the next event of this model at the step and with the blocks
        this model gives."""
        import macro
        mine = {t: b for _, t, b in waves.events(20000)}
        T = Machine.parse(waves.M).table
        seen = 0
        for row in macro.run(2000):
            _, t0, ls, n, cs = row
            cells, head = macro.tape(ls, n, cs)
            cells = [0] * 64 + cells + [0] * (len(cells) + 64)
            head += 64
            last1 = max(i for i, v in enumerate(cells) if v)
            state, t = 0, t0
            while not (state == 0 and head > last1):
                assert 0 < head < len(cells) - 1
                w, d, state = T[state][cells[head]]
                cells[head] = w
                if w and head > last1:
                    last1 = head
                elif not w and head == last1:
                    while not cells[last1]:
                        last1 -= 1
                head += d
                t += 1
            word = "".join(map(str, cells[:head])).lstrip("0")
            self.assertEqual(mine.get(t), [len(x) for x in word.split("0")], (row, t))
            seen += 1
        self.assertEqual(seen, 2001)


class TestC(unittest.TestCase):
    def test_blkrun_matches(self):
        exe = cc(os.path.join(ROOT, "c", "blkrun.c"), "blkrun")
        out = subprocess.run([exe, "2000000"], check=True, capture_output=True, text=True).stdout.split("\n")
        left = [tuple(map(int, x.split()[1:])) for x in out if x.startswith("left")]
        self.assertEqual(left, waves.left_arrivals(2000000))
        end = [x for x in out if x.startswith("end")][0]
        t = waves.START_STEP
        b = list(waves.START)
        for _ in range(2000000):
            b, dt = waves.step(b)
            t += dt
        self.assertEqual(end, f"end 2000000 {t} blocks {len(b)}")


if __name__ == "__main__":
    unittest.main()
