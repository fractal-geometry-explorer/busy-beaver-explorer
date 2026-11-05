"""Checks of the tools behind the study of the top blocks: c/ensemble.c and c/bottom2adic.c against py/waves.py,
c/ensemble_fast.c against c/ensemble.c, and py/top_stats.py.

usage: python3 bb6-1RB1RA_1RC1LB/tests/test_top.py        (a few seconds)
"""
import os
import random
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, "py"))

import waves  # noqa: E402
import top_stats  # noqa: E402

BUILD = tempfile.mkdtemp(prefix="top-test-")


def setUpModule():
    for name, extra in (("ensemble", []), ("ensemble_fast", []), ("bottom2adic", ["-lm"])):
        subprocess.run(["gcc", "-O2", "-Wall", "-Wextra", "-Werror", "-o", os.path.join(BUILD, name),
                        os.path.join(ROOT, "c", name + ".c"), *extra], check=True)


def run(name, *args):
    return subprocess.run([os.path.join(BUILD, name), *map(str, args)], check=True, capture_output=True,
                          text=True).stdout.splitlines()


class Ensemble(unittest.TestCase):
    def test_against_superstep(self):
        """Every return of 200 random orbits (and every halt) is where waves.superstep puts it."""
        out = run("ensemble", 200, 3000, 7, 1, 5, 40, 0)
        starts, rets = {}, {}
        for line in out:
            f = line.split()
            if f[0] == "start":
                starts[int(f[1])] = [int(x) for x in f[2].split(",")]
            elif f[0] == "R":
                rets.setdefault(int(f[1]), []).append((int(f[2]), int(f[3]), int(f[4]), int(f[5])))
        self.assertEqual(len(starts), 200)
        halts = 0
        for i, P in starts.items():
            want = []
            for S in range(1, 3001):
                P2, kind, v = waves.superstep(P)
                if kind != "turn":
                    want.append((S, len(P), v, int(P2 is None)))
                if P2 is None:
                    halts += 1
                    break
                P = P2
            self.assertEqual(rets.get(i, []), want, i)
        self.assertGreater(halts, 0)


class Bottom(unittest.TestCase):
    def test_period_and_profile(self):
        """The last 8 blocks at super step 10^9 come back after their period 4,096, and v2(N) has the profile of
        runs/bottom2adic_18.txt."""
        with open(os.path.join(ROOT, "runs", "superrun_checkpoints.txt")) as f:
            last = f.read().split("\n")[-2].split()
        blocks = list(reversed(last[2:]))[:8]
        out = run("bottom2adic", 8, 0, 4096, *blocks)
        self.assertIn("come back", out[0])
        prof = [line for line in out if line.startswith("v2(N) =")]
        self.assertEqual([line.split(": ")[1].split()[0] for line in prof[:4]], ["1.0000", "0.5000", "1.2500", "1.7500"])

    def test_isolated_bottom_is_the_orbit(self):
        """N mod 2^k from the isolated last k blocks is N mod 2^k of the whole orbit (waves.superstep)."""
        P = [1, 6]
        for _ in range(3000):
            P, _, _ = waves.superstep(P)
        k = 6
        blocks = list(reversed(P))[:k]
        # one super step of the bottom alone, written as in c/bottom2adic.c
        lv = list(blocks)
        for _ in range(500):
            P, _, _ = waves.superstep(P)
            h = 10
            for j in range(k):
                d = lv[j] + h
                if d % 2:
                    lv[j] = (d + 5) // 2
                    if j + 1 < k:
                        lv[j + 1] += (d - 1) // 2
                    break
                lv[j] = h = d // 2
            self.assertEqual((10 + sum(p << j for j, p in enumerate(lv))) % (1 << k), waves.big_n(P) % (1 << k))


class TopStats(unittest.TestCase):
    def test_toppass_counts(self):
        """Waves reaching the k-th block from the left: those that pass it are those that reach block k - 1 (once
        the tables leave at least 8 blocks explicit, so that no wave starts among the top 8)."""
        reach, pas = top_stats.toppass(10 ** 8, depth=8, after=10 ** 6)
        self.assertGreater(reach[0], 0)
        for k in range(1, 8):
            self.assertEqual(pas[k], reach[k - 1])

    def test_n_increases(self):
        """lean/Monotone.lean's theorem, seen on random starts: N grows at every super step."""
        rng = random.Random(3)
        for _ in range(100):
            P = [rng.randint(1, 60) for _ in range(rng.randint(1, 5))]
            N = waves.big_n(P)
            for _ in range(2000):
                P, _, _ = waves.superstep(P)
                if P is None:
                    break
                N2 = waves.big_n(P)
                self.assertGreater(N2, N)
                N = N2


class EnsembleFast(unittest.TestCase):
    def test_same_returns(self):
        """c/ensemble_fast.c -v prints exactly what c/ensemble.c prints (narrow and wide starts, long enough for the
        tables to reach a dozen levels, and the silent bottoms that stop an orbit early)."""
        for args in ((150, 1 << 20, 7, 2, 4, 100, 0), (150, 1 << 18, 303, 1, 8, 1000, 40)):
            self.assertEqual(run("ensemble_fast", "-v", *args), run("ensemble", *args), args)

    def test_totals(self):
        """The totals agree with the returns that -v prints."""
        args = (300, 1 << 18, 11, 2, 6, 5000, 0)
        rets = [line.split() for line in run("ensemble_fast", "-v", *args) if line.startswith("R ")]
        path = os.path.join(BUILD, "fast.txt")
        with open(path, "w") as f:
            f.write("\n".join(run("ensemble_fast", *args)) + "\n")
        tot, cell, inv, pair, rcell = top_stats.read_fast([path])
        self.assertEqual((tot["orbits"], tot["returns"], tot["halts"]),
                         (300, len(rets), sum(int(r[5]) for r in rets)))
        want, kk, k = {}, {}, {}
        for r in rets:
            d = int(r[4])
            b, sv = d.bit_length(), top_stats.v2(d)
            want[b, sv] = want.get((b, sv), 0) + 1
            k[r[1]] = min(k.get(r[1], 0) + 1, 64)
            kk[k[r[1]], b, sv] = kk.get((k[r[1]], b, sv), 0) + 1
        self.assertEqual(dict(cell), want)
        self.assertEqual(dict(rcell), kk)
        for b in {b for b, _ in want}:
            x = sum(1 / int(r[4]) for r in rets if int(r[4]).bit_length() == b)
            self.assertAlmostEqual(inv[b] / x, 1, places=9)

    def test_p_div(self):
        """p_div is 2^-t far from the top of the range, and a log-uniform d1 of b bits is 2^(b-1) with chance
        1/(2^(b-1) ln 2)."""
        self.assertAlmostEqual(top_stats.p_div(40, 8) * 2 ** 8, 1, places=6)
        self.assertAlmostEqual(top_stats.p_div(30, 29), 1 / (2 ** 29 * top_stats.LN2))
        self.assertEqual(top_stats.p_div(10, 10), 0)


class ThinBranch(unittest.TestCase):
    def test_missed_residues(self):
        """Over one period of the last 12 blocks, N mod 2^12 misses exactly 3030 and 4054, and their class 982
        mod 2^10 is visited 5 times instead of 320."""
        Ns, end = top_stats.last_blocks_N()
        self.assertEqual(end, top_stats.LAST12)
        self.assertEqual(sorted(set(range(4096)) - {n % 4096 for n in Ns}), [3030, 4054])
        self.assertEqual(sum(n % 1024 == 982 for n in Ns), 5)


class Branch(unittest.TestCase):
    def test_branch(self):
        """N = 2 mod 4 only at the bottom (12, 26), one step in 8; three steps later N is larger by 106; the thin class
        is -42 mod 2^k, all its visits at (12, 26), and from k = 8 on each follows a wave with v2(N) >= 8
        (= 8 from k = 9)."""
        run = top_stats.bottom_run()
        T = len(run)
        self.assertEqual({r[0][:2] for r in run if r[1] % 4 == 2}, {(12, 26)})
        self.assertEqual(sum(r[1] % 4 == 2 for r in run), T // 8)
        self.assertTrue(all(run[(t + 3) % T][1] == run[t][1] + 106 for t in range(T) if run[t][0][:2] == (12, 26)))
        visits = [sum(r[1] % (1 << k) == -42 % (1 << k) for r in run) for k in range(5, 13)]
        self.assertEqual(visits, [2560, 960, 480, 80, 20, 5, 3, 0])
        deep = [t for t in range(T) if run[t][1] % 256 == -42 % 256]
        self.assertTrue(all(v2_(run[t - 1][1]) >= 8 for t in deep))
        deeper = [t for t in range(T) if run[t][1] % 512 == -42 % 512]
        self.assertTrue(all(v2_(run[t - 1][1]) == 8 for t in deeper))

    def test_other_cycles(self):
        """Other cycles of the last blocks starve other classes: from a few random tapes, the share of 22 mod 32 is
        not the blank-tape orbit's 1/4 on every cycle."""
        rnd = random.Random(1)
        shares = set()
        for _ in range(6):
            c = top_stats.bottom_cycle([rnd.randint(1, 1000) for _ in range(5)], burn=20000, pmax=1 << 14)
            if c:
                P, law = c
                shares.add(law[22] * 32 / P)
        self.assertGreater(len(shares), 1)
        self.assertTrue(any(s > 0.25 for s in shares))


def v2_(x):
    return (x & -x).bit_length() - 1


if __name__ == "__main__":
    unittest.main()
