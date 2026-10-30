"""Checks of c/superrun.c, the super orbit accelerated by periodic tables, against py/waves.py and c/blkrun.c.

usage: python3 bb6-1RB1RA_1RC1LB/tests/test_superrun.py        (about 15 s; SUPERRUN_LONG=1 adds a 2 minute check)
"""
import os
import re
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, "py"))

import waves  # noqa: E402
import superrun as pysuperrun  # noqa: E402
import cycles  # noqa: E402

BUILD = tempfile.mkdtemp(prefix="superrun-test-")
EXE = os.path.join(BUILD, "superrun")


def setUpModule():
    subprocess.run(["gcc", "-O2", "-Wall", "-Wextra", "-Werror", "-o", EXE, os.path.join(ROOT, "c", "superrun.c"),
                    "-lm"], check=True)


def superrun(*args):
    return subprocess.run([EXE, *map(str, args)], check=True, capture_output=True, text=True).stdout.splitlines()


def lefts(out):
    """(S, T, d1, m) of each "left" line, and the HALT line if any."""
    got = []
    for line in out:
        f = line.split()
        if f[0] == "left":
            kv = dict(zip(f[1::2], f[2::2]))
            got.append((int(kv["S"]), int(kv["T"]), int(kv["d1"]), int(kv["m"])))
        elif f[0] == "HALT":
            got.append(("halt", int(f[2]), int(f[4])))
    return got


def py_lefts(P, n):
    """(S, d1, m') of each return to the left end in n super steps of waves.superstep from P, and the halt."""
    got = []
    for s in range(1, n + 1):
        P, kind, v = waves.superstep(P)
        if kind == "halt":
            got.append(("halt", s, v))
            break
        if kind != "turn":
            got.append((s, v, len(P)))
    return got


class TestSuperrun(unittest.TestCase):
    def test_checkpoints_are_waves_events(self):
        """The tape and the machine step after each of the first 4,000 super steps (direct mode) are those of every
        fourth event of waves.step: the per-level step formula is exact."""
        ck = os.path.join(BUILD, "ck.txt")
        superrun("-S", 4000, "-c", ck, 1)
        with open(ck) as f:
            lines = [list(map(int, line.split())) for line in f]
        self.assertEqual(len(lines), 4000)
        want = {}
        for n, t, b in waves.events(3 + 4 * 4000 + 1):
            if n >= 3 and (n - 3) % 4 == 0:
                self.assertEqual(b[-2:], [5, 0])
                want[(n - 3) // 4] = [t] + b[:-2]
        for line in lines:
            self.assertEqual(line[1:], want[line[0]], line[0])

    def test_period_rule(self):
        """Each level's period factor is the orbit length of its block mod 5 under r -> 3^W r + b (lean/Periods.lean),
        so 1, 2, 4 or 5; the cycle spans at most 5 consecutive blocks; and from level 3 on (W >= 7) the pass map
        depends only on the block mod 5 and permutes 5 consecutive blocks.  Levels 0 to 25, about 2 s."""
        rules = [line.split() for line in superrun("-r", "-S", "2e13") if line.startswith("rule")]
        self.assertGreaterEqual(len(rules), 26)  # levels 0 to 25
        for f in rules:
            kv = dict(zip(f[1:13:2], map(int, f[2:13:2])))
            F = list(map(int, f[f.index("F") + 1:]))
            self.assertEqual(kv["L"], int(f[14]), f)
            self.assertIn(kv["L"], (1, 2, 4, 5))
            self.assertEqual({1: 3, 2: 4, 3: 2, 0: 1}[kv["W"] % 4], kv["a"])
            self.assertLessEqual(int(f[16]), 4)
            if kv["W"] >= 7:
                self.assertEqual(F[:5], F[5:10])
                self.assertEqual(sorted(F[:5]), list(range(min(F), min(F) + 5)))

    def test_other_starts(self):
        """From 144 other starts [a, b], direct and accelerated runs return to the left end (and halt) at the same
        super steps with the same d1 as waves.superstep, and both modes agree on the machine steps."""
        halts = 0
        for a in range(1, 13):
            for b in range(1, 13):
                want = py_lefts([a, b], 20000)
                direct = lefts(superrun("-d", "-P", f"{a},{b}", "-S", 20000))
                fast = lefts(superrun("-P", f"{a},{b}", "-S", 20000))
                self.assertEqual(direct, fast, (a, b))
                self.assertEqual([x if x[0] == "halt" else (x[0], x[2], x[3]) for x in direct], want, (a, b))
                halts += bool(want) and want[-1][0] == "halt"
        self.assertGreater(halts, 5)

    def test_cycles(self):
        """py/cycles.py finds the periods of the last 1 to 8 blocks that the tables of c/superrun.c have, and the
        figures of the table on pages/1RB1RA_1RC1LB/reduction.html (§6) for the last 1 to 6."""
        periods = [int(line.split()[8]) for line in superrun("-S", 20000) if line.startswith("table")][:8]
        rows = cycles.table(8)
        self.assertEqual([r[1] for r in rows], periods)
        page = [(4, 3, 11, 14, 4, 2, 2, 1920), (8, 7, 19, 42, 8, 3, 1, 8285), (32, 11, 27, 48, 13, 7, 5, 57413),
                (128, 31, 37, 152, 37, 14, 14, 413014), (256, 60, 70, 380, 48, 11, 17, 1624541),
                (1024, 163, 162, 1042, 98, 21, 23, 14553949)]
        for (k, period, start, tops, waves_, adds, steps), want in zip(rows, page):
            self.assertEqual((period, start, min(tops), max(tops), len(set(tops)), waves_, adds, steps), want, k)

    def test_cycle_gen(self):
        """lean/cycle_gen.py, which writes the kernel check of the tables in pieces, mirrors the Lean definitions: its
        run of the plan for 16 levels and 2 passes ends at the machine step of py/superrun.py, its periods are those
        of the tables of c/superrun.c."""
        sys.path.insert(0, os.path.join(ROOT, "lean"))
        import cycle_gen
        out = tempfile.mkdtemp(prefix="cycle-gen-test-")
        levels = cycle_gen.generate(16, 2, out, verbose=False)
        _, _, T = pysuperrun.lean_plan(16, 2)
        self.assertEqual(levels[-1]["t"], T)
        periods = [int(line.split()[8]) for line in superrun("-S", 10 ** 8) if line.startswith("table")][:16]
        self.assertEqual([lv["period"] for lv in levels[:-1]], periods)
        with open(os.path.join(out, "CycleRun.lean")) as f:
            run = f.read()
        self.assertIn(f"theorem blank_runs_cycles : ∃ c, steps {T} init = some c", run)
        self.assertIn("theorem cycle16 :", run)

    def test_accelerated_matches_direct(self):
        """From blank tape, the accelerated run and the direct run agree on every return to the left end in the first
        3·10^8 super steps (S, machine step, d1, m), and the tables do get built."""
        fast = superrun("-S", 3 * 10 ** 8)
        self.assertTrue(any(line.startswith("table K 16") for line in fast))
        direct = lefts(superrun("-d", "-S", 3 * 10 ** 8))
        self.assertEqual(lefts(fast), direct)
        self.assertEqual(len(direct), 13)

    def test_blkrun_left_arrivals(self):
        """The returns to the left end up to 1.75·10^10 super steps are those of runs/left_arrivals_macro.txt
        (c/blkrun.c, 7·10^10 macro steps): macro step 4S + 2, wave value c = d1 - 4 on arrival.  (Its first arrival,
        at macro step 1, is before the first super step.)"""
        fast = lefts(superrun("-S", 17500000000))
        with open(os.path.join(ROOT, "runs", "left_arrivals_macro.txt")) as f:
            rows = [re.match(r"left k=(\d+) step=(\d+) c=(\d+)", line) for line in f]
        first = {}
        for r in filter(None, rows):
            first.setdefault(int(r[1]), int(r[3]))
        self.assertEqual(first.pop(1), 2)
        self.assertEqual(len(first), 15)
        self.assertEqual({4 * s + 2: d1 - 4 for s, t, d1, m in fast}, first)

    def test_python_version(self):
        """py/superrun.py, the same method written again in Python with big integers, gives the same returns to the
        left end (S, machine step, d1, m) up to 10^14 super steps, and the same halts from other starts."""
        self.assertEqual(lefts(superrun("-S", 10 ** 14)), list(pysuperrun.run(10 ** 14)))
        for a, b in [(3, 5), (1, 1), (2, 7), (9, 4), (12, 12)]:
            self.assertEqual(lefts(superrun("-P", f"{a},{b}", "-S", 10 ** 6)),
                             list(pysuperrun.run(10 ** 6, [a, b])), (a, b))

    @unittest.skipUnless(os.environ.get("SUPERRUN_LONG"), "set SUPERRUN_LONG=1 (about 2 minutes)")
    def test_blkrun_machine_step(self):
        """c/blkrun.c run to the end of super step 867,796,127 (macro step 4S + 3) ends at the machine step the
        accelerated run gives there.  (With S = 3,582,299,143 the same holds, at step 1,418,025,594,627,195,513,086;
        that takes blkrun about 5 minutes.)"""
        s = 867796127
        fast = [x for x in lefts(superrun("-S", s)) if x[0] == s]
        exe = os.path.join(BUILD, "blkrun")
        subprocess.run(["gcc", "-O2", "-o", exe, os.path.join(ROOT, "c", "blkrun.c")], check=True)
        out = subprocess.run([exe, str(4 * s + 3)], check=True, capture_output=True, text=True).stdout.splitlines()
        self.assertEqual(out[-1].split()[:3], ["end", str(4 * s + 3), str(fast[0][1])])


if __name__ == "__main__":
    unittest.main()
