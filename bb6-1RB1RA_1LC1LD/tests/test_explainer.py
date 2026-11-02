"""Checks of the engine of pages/1RB1RA_1LC1LD/explainer.html against py/macro.py and the reference simulator.

The page runs the machine and the pass map in the browser. This test takes the page's engine (the
`<script id="engine">` block) and its run data (`<script id="run-data">`), runs them in Node, and compares them with
the reference simulator (tools/py/bbtools, through `macro.pass_starts`), with `macro.next_full` and `macro.offset`
(the Python transcription of `pass` in lean/Recur.lean and of `pre` in lean/Formula.lean), and with the end of the run
that lean/Count.lean evaluates (`blank_reaches_1e12`).  Skipped if `node` is not installed.

usage: python3 bb6-1RB1RA_1LC1LD/tests/test_explainer.py        (a few seconds)
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
PAGE = os.path.join(REPO, "pages", "1RB1RA_1LC1LD", "explainer.html")
sys.path.insert(0, os.path.join(REPO, "tools", "py"))
sys.path.insert(0, os.path.join(ROOT, "py"))

import blocks  # noqa: E402
import macro  # noqa: E402

NODE = shutil.which("node")
RAW_STEPS = 300000


def random_lists(seed, count):
    """Block lists the run need not reach: 1 to 6 blocks of 2..60, half of them with a last block a multiple of 3."""
    rng = random.Random(seed)
    out = []
    for _ in range(count):
        bl = [rng.randint(2, 60) for _ in range(rng.randint(1, 6))]
        if rng.random() < 0.5:
            bl[-1] = 3 * rng.randint(1, 20)
        out.append(bl)
    return out


# Runs in Node after the engine and the run data; prints one JSON object.
DRIVER = r"""
const LISTS = __LISTS__, HALTING = __HALTING__, RAW = __RAW__;
const out = {};
// The bare machine: every pass start (A on a cell never visited before) and its blocks.
{
  const m = makeTM(1 << 14), starts = [];
  while (m.steps < RAW && tmStep(m)) if (isPassStart(m)) starts.push([m.steps, blocksOf(m)]);
  out.raw = starts;
}
// The pass map, both versions, and the offset c of a recursive pass.
out.lists = LISTS.map(bl => {
  const f = nextFull(bl), s = nextFullSlow(bl);
  const o = bl.length >= 2 && bl[bl.length - 1] % 3 === 0 ? offsetOf(bl.slice(0, -1).reverse()) : null;
  return [f, s, o ? [o.c, o.u] : null];
});
// The halting starts of py/blocks.py: the path to the halt.
out.halting = HALTING.map(bl => {
  const path = [bl];
  for (let k = 0; k < 12 && Array.isArray(path[path.length - 1]); k++) path.push(nextFull(path[path.length - 1]));
  return path;
});
// The run from 10 3, recomputed, against the page's data.
{
  let b = [10, 3], ok = true, first = null;
  for (let i = 0; i <= 8257; i++) {
    const tot = b.reduce((a, c) => a + c, 0);
    if (RUN.L[i] !== b[b.length - 1] || RUN.T[i] !== tot || RUN.K[i] !== b.length) { ok = false; first = i; break; }
    if (i < 8257) b = nextFull(b);
  }
  out.run = { ok, first, n: RUN.L.length, end: b, recursive: RUN.L.slice(0, 8257).filter(x => x % 3 === 0).length };
}
console.log(JSON.stringify(out));
"""


def script_of(name):
    with open(PAGE) as f:
        html = f.read()
    m = re.search(r'<script id="%s">(.*?)</script>' % name, html, re.S)
    if not m:
        raise AssertionError(f"no <script id=\"{name}\"> in {PAGE}")
    return m.group(1)


@unittest.skipUnless(NODE, "node is not installed")
class TestExplainer(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lists = random_lists(1, 400) + [list(b) for b in blocks.HALTING_STARTS] + [[3, 6], [2, 2, 3], [4, 3, 6]]
        driver = (DRIVER.replace("__LISTS__", json.dumps(cls.lists))
                  .replace("__HALTING__", json.dumps([list(b) for b in blocks.HALTING_STARTS] + [[3, 6], [2, 2, 3]]))
                  .replace("__RAW__", str(RAW_STEPS)))
        src = script_of("engine") + "\n" + script_of("run-data") + "\n" + driver
        with tempfile.NamedTemporaryFile("w", suffix=".js", delete=False) as f:
            f.write(src)
            path = f.name
        try:
            res = subprocess.run([NODE, path], check=True, capture_output=True, text=True, timeout=600)
        finally:
            os.unlink(path)
        cls.out = json.loads(res.stdout)

    def test_raw_pass_starts(self):
        """The page's simulator finds the same pass starts, at the same steps, as the reference simulator."""
        want = [[t, list(bl)] for t, bl in macro.pass_starts(RAW_STEPS)]
        self.assertGreater(len(want), 50)
        self.assertEqual(self.out["raw"], want)

    def test_pass_map(self):
        """Both versions of the page's pass map agree with macro.next_full, and the offsets with macro.offset."""
        for bl, (fast, slow, off) in zip(self.lists, self.out["lists"]):
            r = macro.next_full(tuple(bl))
            want = r if r in (None, macro.HALT) else list(r)
            self.assertEqual(fast, want, bl)
            self.assertEqual(slow, want, bl)
            if off is not None:
                self.assertEqual(tuple(off), macro.offset(list(reversed(bl[:-1]))), bl)

    def test_halting_starts(self):
        """Every halting start of py/blocks.py halts in the page, and 16 16 by the path of `sixteen_halts`."""
        for path in self.out["halting"]:
            self.assertEqual(path[-1], macro.HALT, path[0])
        sixteen = next(p for p in self.out["halting"] if p[0] == [16, 16])
        self.assertEqual(sixteen, [[16, 16], [26, 9], [6, 27, 6], [14, 27, 4], [14, 33, 1], macro.HALT])

    def test_run_data(self):
        """The page's run data is the engine's run from 10 3, and ends where lean/Count.lean does."""
        run = self.out["run"]
        self.assertTrue(run["ok"], f"run data differs from the engine at pass {run['first']}")
        self.assertEqual(run["n"], 8258)
        self.assertEqual(run["end"], [11866, 17246])
        self.assertEqual(run["recursive"], 2654)


if __name__ == "__main__":
    unittest.main()
