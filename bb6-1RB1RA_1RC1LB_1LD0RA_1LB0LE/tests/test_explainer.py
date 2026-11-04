"""Checks of pages/1RB1RA_1RC1LB_1LD0RA_1LB0LE/explainer.html: its engine against py/passmap.py and the reference
simulator, and its status panel against status.json.

The test takes the page's engine (the `<script id="engine">` block), runs it in Node and compares the bare machine with
tools/py/bbtools, the pass starts from blank tape with the orbit of the closed form, and the page's closed form and
single passes with `passmap` and `run_pass`. Skipped if `node` is not installed (the status check still runs).

usage: python3 bb6-1RB1RA_1RC1LB_1LD0RA_1LB0LE/tests/test_explainer.py        (a few seconds)
"""
import json
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
REPO = os.path.dirname(ROOT)
sys.path.insert(0, os.path.join(REPO, "tools", "py"))
sys.path.insert(0, os.path.join(ROOT, "py"))

import explainer_status  # noqa: E402
import passmap  # noqa: E402
from bbtools.machine import Machine, Run  # noqa: E402

NODE = shutil.which("node")
STEPS = [0, 1, 2, 5, 17, 41, 100, 1000, 12345, 200000]

rnd = random.Random(11)
LISTS = [[2, 1, 1], [4, 5], [5, 7, 1, 1], [2, 2], [3, 4, 2, 5], [7, 6], [1, 7, 4], [12, 24], [2, 1], [4, 2, 3]]
LISTS += [[rnd.randint(1, 12) for _ in range(rnd.randint(1, 7))] for _ in range(400)]

# Runs in Node after the engine; prints one JSON object.
DRIVER = r"""
const LISTS = %s, STEPS = %s;
const out = {};
out.raw = STEPS.map(t => { const m = new BB.Raw(); m.run(t); return [t, m.lo, m.cells(), m.h, m.halted ? "H" : BB.S[m.q], m.ones]; });
{
  const m = new BB.Raw(), starts = [];
  while (starts.length < 150) { if (m.toPass(1e8) !== "pass") break; const b = m.blocks(); starts.push([m.t, b.y, b.clean, m.ones]); }
  out.starts = starts;
}
out.passmap = LISTS.map(y => BB.passmap(y));
out.stop = LISTS.map(y => BB.stopIndex(y));
out.pass = LISTS.map(y => { const r = BB.runPass(y); return [r.kind === "halt" ? "HALT" : r.y, r.t, r.kind === "halt" ? true : r.clean]; });
{
  const seen = [];
  const end = BB.orbit(3000, (i, y, j) => { if (i < 300) seen.push(y); });
  out.orbit = { seen, end };
}
// The phase labels of one pass from [3, 4, 2, 5], step by step.
{
  const m = BB.fromBlocks([3, 4, 2, 5]), ph = [];
  let p = "start", k = 0;
  for (;;) { const s = m.step(); if (s.passStart || s.halt) break; p = BB.phase(p, s, k++); ph.push(p); }
  out.phases = ph;
}
console.log(JSON.stringify(out));
"""


def state_at(t):
    r = Run(Machine.parse(passmap.M))
    halted = r.run(t)
    return r, halted


@unittest.skipIf(NODE is None, "node is not installed")
class TestEngine(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        with open(explainer_status.PAGE) as f:
            m = re.search(r'<script id="engine">(.*?)</script>', f.read(), re.S)
        assert m, "no engine script in the page"
        with tempfile.NamedTemporaryFile("w", suffix=".js", delete=False) as f:
            f.write(m.group(1) + DRIVER % (json.dumps(LISTS), json.dumps(STEPS)))
            path = f.name
        try:
            cls.out = json.loads(subprocess.run([NODE, path], check=True, capture_output=True, text=True).stdout)
        finally:
            os.unlink(path)

    def test_raw_machine(self):
        """The page's simulator against the reference simulator, tape, head and state, from blank tape."""
        for t, lo, cells, h, q, ones in self.out["raw"]:
            r, _ = state_at(t)
            self.assertEqual(r.steps, t)
            want = {i: r.tape.get(i) for i in range(min(lo, r.tape.lo), max(lo + len(cells), r.tape.hi + 1))}
            got = {i: cells[i - lo] if 0 <= i - lo < len(cells) else 0 for i in want}
            self.assertEqual(got, want, t)
            self.assertEqual((h, q, ones), (r.head, "ABCDEF"[r.state], sum(want.values())), t)

    def test_pass_starts(self):
        """The page's pass starts from blank tape: the first at step 17 (`blank_at_17`), every one clean, with 4(n+1)
        ones, and the block lists the orbit of the closed form."""
        st = self.out["starts"]
        self.assertEqual(len(st), 150)
        self.assertEqual(st[0][:2], [17, [2, 2]])
        self.assertEqual([y for _, y, _, _ in st], list(passmap.orbit(150)))
        for n, (_, y, clean, ones) in enumerate(st):
            self.assertTrue(clean, n)
            self.assertEqual(ones, 4 * (n + 1))
        times = [t for t, _, _, _ in st]
        self.assertEqual(times, sorted(times))

    def test_passmap(self):
        """The page's closed form and stop index equal py/passmap.py, halts and stop blocks of 1 included."""
        for y, got, j in zip(LISTS, self.out["passmap"], self.out["stop"]):
            want = passmap.passmap(y)
            self.assertEqual(got, "halt" if want == passmap.HALT else want, y)
            self.assertEqual(j, passmap.stop_index(y), y)

    def test_run_pass(self):
        """One pass on the page's machine equals `run_pass`: the next list (or the halt), and the step count."""
        for y, (got, t, clean) in zip(LISTS, self.out["pass"]):
            want, wt, wclean = passmap.run_pass(y)
            self.assertEqual((got, clean), (want, wclean), y)
            self.assertEqual(t, wt, y)

    def test_examples(self):
        """The examples of part 6: [2, 1, 1] goes to [4, 5], which halts; [5, 7, 1, 1] goes to [9, 10]."""
        got = dict((json.dumps(y), p) for y, p in zip(LISTS, self.out["pass"]))
        self.assertEqual(got["[2, 1, 1]"][0], [4, 5])
        self.assertEqual(got["[4, 5]"][0], "HALT")
        self.assertEqual(got["[5, 7, 1, 1]"][0], [9, 10])

    def test_orbit(self):
        o = self.out["orbit"]
        self.assertEqual(o["seen"], list(passmap.orbit(300)))
        self.assertEqual(o["end"]["i"], 3000)
        self.assertIsNone(o["end"]["end"])

    def test_phases(self):
        """The pass from [3, 4, 2, 5] goes start, sweep (with crossings), stop, zigzag, in that order."""
        ph = self.out["phases"]
        self.assertEqual(ph[:3], ["start"] * 3)
        order = [p for i, p in enumerate(ph) if i == 0 or ph[i - 1] != p]
        self.assertEqual(order[0], "start")
        self.assertEqual(order[-2:], ["stop", "zigzag"])
        self.assertEqual(set(order[1:-2]), {"sweep", "cross"})
        self.assertEqual(order.count("cross"), 3)     # into 2, into 4, into 3


class TestStatus(unittest.TestCase):
    def test_status_current(self):
        """The status panel holds the claims of status.json (run py/explainer_status.py after editing it)."""
        with open(explainer_status.STATUS) as f:
            spec = json.load(f)
        with open(explainer_status.PAGE) as f:
            page = f.read()
        self.assertEqual(page, explainer_status.build(page, spec))
        levels = {c["level"] for c in spec["claims"]}
        self.assertLessEqual(levels, {"kernel", "native", "trusted", "heuristic", "open"})


if __name__ == "__main__":
    unittest.main(verbosity=2)
