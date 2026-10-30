"""Checks of the engine of pages/1RB1RA_1RC1LB/explainer.html against the models here and direct simulation.

The page runs the machine and its four coarser descriptions in the browser. This test takes the page's engine (the
`<script id="engine">` block), runs it in Node, and compares it with the reference simulator (tools/py/bbtools),
py/macro.py (the map that lean/Macro.lean proves) and py/waves.py. Skipped if `node` is not installed.

usage: python3 bb6-1RB1RA_1RC1LB/tests/test_explainer.py        (a few seconds)
"""
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
REPO = os.path.dirname(ROOT)
PAGE = os.path.join(REPO, "pages", "1RB1RA_1RC1LB", "explainer.html")
sys.path.insert(0, os.path.join(REPO, "tools", "py"))
sys.path.insert(0, os.path.join(ROOT, "py"))

from bbtools.machine import Machine, Run  # noqa: E402
import cycles  # noqa: E402
import macro  # noqa: E402
import waves  # noqa: E402

NODE = shutil.which("node")

# Runs in Node after the engine; prints one JSON object.
DRIVER = r"""
const eq = (a, b) => JSON.stringify(a) === JSON.stringify(b);
const out = {};
// The bare machine at a few steps.
out.raw = [0, 1, 2, 5, 17, 68, 136, 1000, 5000, 100000].map(t => [t, BB.rawPicture(BB.rawAt(t))]);
// Rule by rule: every picture against the engine's own machine, the first ones also printed for Python.
{
  let c = { kind: "blank", ls: [] }, m = new BB.Raw(), bad = null, n = 0;
  const first = [], rules = {};
  for (; n < 20000; n++) {
    const r = BB.ruleStep(c);
    rules[r.rule] = (rules[r.rule] || 0) + 1;
    m.run(r.t, false); c = r.next;
    const p = BB.rulePicture(c);
    if (!eq(p, BB.rawPicture(m))) { bad = [n, r.rule]; break; }
    if (n < 400) first.push([m.t, p]);
  }
  out.rules = { n, bad, first, counts: rules, t: m.t };
}
// Macro steps.
{
  let x = { ls: [1], n: 2, cs: [] }, t = 15;
  const run = [[0, t, x.ls, x.n, x.cs]];
  for (let k = 1; k <= 1000; k++) { const r = BB.macroStep(x); t += r.t; x = r.next; run.push([k, t, x.ls, x.n, x.cs]); }
  out.macro = run;
  out.halts = [[[2, 2, 2], 1, [3]], [[1], 3, []], [[2], 5, [1, 1]], [[2, 2], 1, []]].map(([ls, n, cs]) => {
    const r = BB.macroStep({ ls, n, cs });
    return [ls, n, cs, r.halted, r.t];
  });
}
// Wave events.
{
  let b = BB.WAVE_START.b.slice(), t = BB.WAVE_START.t;
  const ev = [];
  for (let k = 0; k < 3000; k++) { ev.push([k, t.toString(), b]); const r = BB.waveStep(b); b = r.b; t += r.t; }
  out.events = ev;
}
// Super steps, by the formula and by four waves.
{
  let P = BB.SUPER_START.P.slice(), t = BB.SUPER_START.t, disagree = null;
  const sup = [];
  for (let k = 0; k < 3000; k++) {
    const s = BB.superStep(P), w = BB.superByWaves(P);
    sup.push([P, s.kind, BB.bigN(P).toString(), t.toString()]);
    if (!eq(w.b, [...s.next, 5, 0])) { disagree = k; break; }
    t += w.t; P = s.next;
  }
  out.super = { sup, disagree };
  out.custom = [[1, 4], [2, 1, 4], [1, 4, 4, 6], [3, 1, 1]].map(P => [P, BB.superStep(P).kind, BB.bigN(P).toString(), !!BB.superByWaves(P).halted]);
}
// The last blocks on their own: bottomStep against the super step, what they send on, and their cycles.
{
  let P = BB.SUPER_START.P.slice(), bad = null;
  const outs = [];
  for (let s = 0; s < 3000 && !bad; s++) {
    const next = BB.superStep(P).next;
    for (let k = 1; k < P.length; k++) {
      const r = BB.bottomStep(BB.bottom(P, k));
      if (!eq(r.next, BB.bottom(next, k))) { bad = [s, k]; break; }
      if (s < 300 && k <= 4) outs.push([BB.bottom(P, k), r.next, r.out]);
    }
    P = next;
  }
  out.bottom = { bad, outs, cycles: [1, 2, 3, 4, 5, 6, 7, 8].map(k => BB.findCycle(k)) };
}
console.log(JSON.stringify(out));
"""


def picture(cells, head, state):
    """As `picture` in the engine: cells trimmed to the first and last 1, keeping the head's cell."""
    a, b = 0, len(cells) - 1
    while a < head and cells[a] == 0:
        a += 1
    while b > head and cells[b] == 0:
        b -= 1
    return {"cells": cells[a:b + 1], "head": head - a, "state": state}


def direct(t):
    r = Run(Machine.parse(waves.M))
    r.run(t)
    lo, hi = min(r.tape.lo, r.head) - 1, max(r.tape.hi, r.head) + 1
    return picture(r.tape.word(lo, hi), r.head - lo, "ABCDEF"[r.state])


@unittest.skipIf(NODE is None, "node is not installed")
class TestExplainer(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        with open(PAGE) as f:
            m = re.search(r'<script id="engine">(.*?)</script>', f.read(), re.S)
        assert m, "no engine script in the page"
        with tempfile.NamedTemporaryFile("w", suffix=".js", delete=False) as f:
            f.write(m.group(1) + DRIVER)
            path = f.name
        try:
            cls.out = json.loads(subprocess.run([NODE, path], check=True, capture_output=True, text=True).stdout)
        finally:
            os.unlink(path)

    def test_raw_machine(self):
        """The page's simulator against the reference simulator."""
        for t, pic in self.out["raw"]:
            self.assertEqual(pic, direct(t), t)

    def test_rules(self):
        """20,000 block moves, each picture equal to the machine's tape at that step; the first 400 also against the
        reference simulator. Every rule but the halt is used."""
        r = self.out["rules"]
        self.assertIsNone(r["bad"])
        self.assertEqual(r["n"], 20000)
        self.assertEqual(set(r["counts"]), {"start", "transfer", "empty_start", "sweep_step", "sweep_end",
                                            "carry_start", "carry_two", "carry_exit", "carry_one"})
        run = Run(Machine.parse(waves.M))
        for t, pic in r["first"]:
            run.run(t)
            lo, hi = min(run.tape.lo, run.head) - 1, max(run.tape.hi, run.head) + 1
            self.assertEqual(pic, picture(run.tape.word(lo, hi), run.head - lo, "ABCDEF"[run.state]), t)

    def test_macro(self):
        """1,000 macro steps equal py/macro.py, step counts included (1,322,171 steps, as Lean's runM_1000)."""
        self.assertEqual(self.out["macro"], [list(row) for row in macro.run(1000)])
        self.assertEqual(self.out["macro"][-1][1], 1322171)

    def test_halts(self):
        """The halting macro steps, as py/macro.py: halted, with the same step count."""
        for ls, n, cs, halted, t in self.out["halts"]:
            want = macro.next_step(ls, n, cs)
            self.assertEqual(halted, want[0] == "halt", (ls, n, cs))
            if halted:
                self.assertEqual(t, want[1])

    def test_events(self):
        """3,000 wave events equal py/waves.py."""
        want = [[k, str(t), b] for k, t, b in waves.events(3000)]
        self.assertEqual(self.out["events"], want)

    def test_super(self):
        """3,000 super steps: the formula agrees with four waves, and the lists, kinds and N equal py/waves.py."""
        s = self.out["super"]
        self.assertIsNone(s["disagree"])
        P = [1, 6]
        for got_P, kind, N, _ in s["sup"]:
            self.assertEqual(got_P, P)
            P2, want_kind, _ = waves.superstep(P)
            self.assertEqual((kind, int(N)), (want_kind, waves.big_n(P)))
            P = P2
        self.assertEqual(s["sup"][0][3], "136")

    def test_custom(self):
        """Lists typed into the page: N a power of two halts, by the formula and by the waves."""
        for P, kind, N, halted in self.out["custom"]:
            self.assertEqual(kind, waves.superstep(P)[1])
            self.assertEqual(int(N), waves.big_n(P))
            n = int(N)
            self.assertEqual(halted, n & (n - 1) == 0, P)
            self.assertEqual(kind == "halt", halted, P)

    def test_bottom(self):
        """Level 5: the last k blocks of the next super step follow from the last k blocks alone (`bottomStep`, as
        `bstep` in py/cycles.py and lean/Cascade.lean), and the cycles the page finds are those of py/cycles.py and,
        for the last 1 to 6 blocks, those of `cycle_1` to `cycle_6` in lean/Cycles.lean."""
        b = self.out["bottom"]
        self.assertIsNone(b["bad"])
        for B, nxt, ev in b["outs"]:
            want, want_ev, _ = cycles.bstep(B)
            self.assertEqual(nxt, want)
            self.assertEqual(None if ev is None else (ev["kind"], ev.get("h", ev.get("a"))), want_ev)
        lean = [(4, 3), (8, 7), (32, 11), (128, 31), (256, 60), (1024, 163)]
        rows = cycles.table(8)
        for k, got in enumerate(b["cycles"], 1):
            self.assertEqual((got["period"], got["start"]), rows[k - 1][1:3], k)
            if k <= 6:
                self.assertEqual((got["period"], got["start"]), lean[k - 1], k)


if __name__ == "__main__":
    unittest.main()
