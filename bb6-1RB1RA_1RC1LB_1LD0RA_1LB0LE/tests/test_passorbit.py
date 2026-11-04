"""Checks c/passorbit.c, the fast closed-form pass map, against py/passmap.py and the machine (CI runs them,
.github/workflows/tests.yml).

usage: python3 bb6-1RB1RA_1RC1LB_1LD0RA_1LB0LE/tests/test_passorbit.py
"""
import os
import re
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
REPO = os.path.dirname(ROOT)
sys.path.insert(0, os.path.join(ROOT, "py"))
sys.path.insert(0, os.path.join(REPO, "tools", "py"))

import merge_parts  # noqa: E402
import passmap  # noqa: E402
import passorbit  # noqa: E402

PO = passorbit.build()


def run(*args, env=None):
    e = dict(os.environ)
    e.update(env or {})
    return subprocess.run([PO] + [str(a) for a in args], capture_output=True, text=True, check=True, env=e).stdout


def sums(text):
    return {m.group(1): int(m.group(2)) for m in re.finditer(r"^sum (\S+) (\d+)$", text, re.M) if int(m.group(2))}


def events(text):
    """{start list: (kind, pass)} from the `event` lines."""
    out = {}
    for m in re.finditer(r"^event (\S+) start (\[[^\]]*\]) pass (\d+)$", text, re.M):
        out[tuple(eval(m.group(2)))] = (m.group(1), int(m.group(3)))
    return out


def first_event(y, p):
    """(kind, pass) of the first event from y in p passes by passmap, or None."""
    for t in range(p):
        z = passmap.passmap(y)
        if z is None:
            return "stop_block_1", t
        if z == passmap.HALT:
            return "halt", t
        y = z
    return None


class TestLoose(unittest.TestCase):
    def test_loose(self):
        """`passorbit loose`: the sentinel orbit from [1, 3], first pass with each block count, as
        py/blockcount.py's loose_firsts (to 3*10^5 passes)."""
        import blockcount
        out = run("loose", 300000)
        got = {int(m.group(1)): (int(m.group(2)), list(eval(m.group(3))))
               for m in re.finditer(r"^(\d+) blocks first at pass (\d+): (\[.*\])$", out, re.M)}
        want = blockcount.loose_firsts(300000)
        self.assertEqual(got, {k: v for k, v in want.items() if k > 2})
        self.assertEqual(got[7][0], 269206)


class TestOrbit(unittest.TestCase):
    def test_checkpoints(self):
        """Every checkpoint (the list and the hash of the whole run) of the first 10^5 passes equals passmap's."""
        self.assertEqual(passorbit.check(100000), [1, 10, 100, 1000, 10000, 100000])

    def test_statistics(self):
        """The statistics of 2*10^5 passes from [2, 2] agree with py/passmap.py."""
        out = run("orbit", 200000)
        ks, smallest = {}, None
        for i, y in enumerate(passmap.orbit(200000)):
            ks[len(y)] = ks.get(len(y), 0) + 1
            j = passmap.stop_index(y)
            if i >= 50 and j < len(y) and (smallest is None or y[j - 1] < smallest):
                smallest = y[j - 1]
        line = re.search(r"^block_counts (.*)$", out, re.M).group(1)
        self.assertEqual(dict(map(int, kv.split(":")) for kv in line.split()), ks)
        self.assertEqual(int(re.search(r"^min_stop_after_50 (\d+)", out, re.M).group(1)), smallest)
        self.assertIn("event ok", out)

    def test_event_stops(self):
        """From a list whose orbit meets a stop block of 1 the run stops there, as passmap does."""
        out = run("orbit", 100, 6, 3, 7)
        self.assertIn("event stop_block_1 at pass 1 (0-based) list [1, 14, 5]", out)
        self.assertEqual(passmap.passmap([6, 3, 7]), [1, 14, 5])
        self.assertIsNone(passmap.passmap([1, 14, 5]))


class TestFamilies(unittest.TestCase):
    def test_comps(self):
        """Every list of 1 to 13 ones: the counts by event and sum mod 4 equal passmap's, split or not."""
        one = run("comps", 1, 13, 200, 0, 1)
        self.assertEqual({k: v for k, v in sums(one).items() if "_sum_mod4_" in k}, passorbit.comps(1, 13, 200))
        d = tempfile.mkdtemp()
        paths = []
        for p in range(3):
            path = os.path.join(d, f"part_{p}.txt")
            with open(path, "w") as f:
                f.write(run("comps", 1, 13, 200, p, 3))
            paths.append(path)
        out, problems = merge_parts.merge(paths)
        self.assertEqual(problems, [])
        self.assertEqual(sums("\n".join(out)), sums(one))

    def test_grid_events(self):
        """Every two-block start [a, b] up to 40: each event, its kind and pass, as passmap gives them."""
        out = run("grid", 40, 40, 300, 0, 1, env={"PASSORBIT_EVENTS": "100000"})
        got = events(out)
        want = {}
        for a in range(1, 41):
            for b in range(1, 41):
                e = first_event([a, b], 300)
                if e:
                    want[(a, b)] = e
        self.assertEqual(got, want)

    def test_random_parts(self):
        """The random starts split into parts give the counts of one run."""
        one = sums(run("random", 3000, 6, 50, 500, 5, 0, 1))
        tot = {}
        for p in range(4):
            for k, v in sums(run("random", 3000, 6, 50, 500, 5, p, 4)).items():
                tot[k] = tot.get(k, 0) + v
        self.assertEqual(tot, one)
        self.assertEqual(sum(v for k, v in one.items() if "_sum_mod4_" in k), 3000)

    def test_two_pass_family(self):
        """[x, 3, z] with x = 2 and z = 3 mod 4 meets a stop block of 1 on its second pass; no other residues of
        [x, 3, z] with 4 | x + 3 + z do in 300 passes (x, z < 120)."""
        for x in range(1, 120):
            for z in range(1, 120):
                if (x + 3 + z) % 4:
                    continue
                e = first_event([x, 3, z], 300)
                if x % 4 == 2 and z % 4 == 3:
                    self.assertEqual(e, ("stop_block_1", 1))
                    self.assertEqual(passmap.passmap([x, 3, z]), [1, x + 2 + (z + 5) // 2, (z + 5) // 2 - 1])
                else:
                    self.assertIsNone(e, (x, z))

    def test_two_pass_family_halts_on_machine(self):
        """On the machine itself, members of that family halt a few passes later."""
        for y in ([2, 3, 3], [6, 3, 7], [10, 3, 11], [30, 3, 15], [62, 3, 63]):
            for _ in range(20):
                z, _, clean = passmap.run_pass(y, 10 ** 8)
                self.assertTrue(clean)
                if z == passmap.HALT:
                    break
                y = z
            self.assertEqual(z, passmap.HALT)


if __name__ == "__main__":
    unittest.main(verbosity=2)
