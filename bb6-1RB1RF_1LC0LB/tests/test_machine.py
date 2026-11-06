"""Checks on this machine's generated files, its pages and the observations of notes/LAB_NOTES.md (CI runs them,
.github/workflows/tests.yml).

usage: python3 bb6-1RB1RF_1LC0LB/tests/test_machine.py        (a few seconds)
"""
import json
import os
import subprocess
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
REPO = os.path.dirname(ROOT)
TOOLS = os.path.join(REPO, "tools")
sys.path.insert(0, os.path.join(TOOLS, "py"))
sys.path.insert(0, os.path.join(TOOLS, "pages"))
sys.path.insert(0, os.path.join(ROOT, "py"))

import blank  # noqa: E402
import counter  # noqa: E402
import accel  # noqa: E402
import replay  # noqa: E402
import top  # noqa: E402
import build_status  # noqa: E402
from bbtools.invariants import conserved  # noqa: E402
from bbtools.leangen import machine_lean  # noqa: E402
from bbtools.machine import Run  # noqa: E402

M = "1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE---"
LEFT = os.path.join(ROOT, "runs", "left_1e10.txt")


class TestGenerated(unittest.TestCase):
    def test_machine_lean_current(self):
        with open(os.path.join(ROOT, "lean", "Machine.lean")) as f:
            src = f.read()
        doc = "The six-state machine this folder studies; whether it halts from blank tape is open."
        self.assertEqual(src, machine_lean(M, "BB6e", doc))

    def test_rules_lean_current(self):
        out = subprocess.run([sys.executable, os.path.join(ROOT, "lean", "rules.py")], check=True,
                             capture_output=True, text=True).stdout
        with open(os.path.join(ROOT, "lean", "Rules.lean")) as f:
            self.assertEqual(f.read(), out)

    def test_top_lean_current(self):
        sys.path.insert(0, os.path.join(ROOT, "lean"))
        import top_gen
        made = top_gen.files()
        import glob
        have = {os.path.basename(p) for p in glob.glob(os.path.join(ROOT, "lean", "TopWall*.lean"))} | {"Top.lean",
                                                                                               "TopFam.lean",
                                                                                               "AxiomsWall.lean"}
        self.assertEqual(set(made), have)
        for name, text in made.items():
            with open(os.path.join(ROOT, "lean", name)) as f:
                self.assertEqual(f.read(), text, name)

    def test_rework_lean_current(self):
        sys.path.insert(0, os.path.join(ROOT, "lean"))
        import rework_gen
        with open(os.path.join(ROOT, "lean", "Rework.lean")) as f:
            self.assertEqual(f.read(), rework_gen.text()[0])

    def test_page_current(self):
        with open(os.path.join(ROOT, "status.json")) as f:
            spec = json.load(f)
        spec.setdefault("source", "bb6-1RB1RF_1LC0LB/status.json")
        with open(os.path.join(REPO, "pages", "1RB1RF_1LC0LB", "proof-status.html")) as f:
            self.assertEqual(f.read(), build_status.build(spec, spec.get("home", "../index.html")))


class TestRun(unittest.TestCase):
    def test_machine(self):
        self.assertEqual(blank.MACHINE.halting_transitions(), ["F1"])

    def test_no_halt_early(self):
        self.assertEqual(blank.summary(10 ** 6), (False, 10 ** 6, 1188, 2377))

    def test_halting_shape_on_run(self):
        """`d_right_zero` and `a_entry` on the run: D always has a 0 to its right, A always comes from E on a 0."""
        r = Run(blank.MACHINE)
        prev = None
        while r.steps < 200000:
            if r.state == blank.D:
                self.assertEqual(r.tape.get(r.head + 1), 0, r.steps)
            if r.state == blank.A and prev is not None:
                self.assertEqual(prev, (blank.E, 0), r.steps)
            prev = (r.state, r.tape.get(r.head))
            self.assertTrue(r.step())

    def test_left_events_match_c(self):
        """py/blank.py left gives the first lines of runs/left_1e10.txt (written by tools/c/tokrun)."""
        with open(LEFT) as f:
            c_lines = [line.rstrip("\n") for line in f][:24]
        py = [f"{t} L {w} {s} {ws}" for t, w, s, ws in blank.left_events(3 * 10 ** 6)][:24]
        self.assertEqual(py, c_lines)

    def test_growth_file(self):
        with open(os.path.join(ROOT, "runs", "growth_1e10.txt")) as f:
            rows = [list(map(int, line.split())) for line in f]
        self.assertEqual(rows[-1], [10 ** 10, 258671, 129335, 207])
        for t, w, ones, _ in rows[:13]:     # up to 10^5 steps
            h, t2, o2, w2 = blank.summary(t)
            self.assertEqual((h, t2, o2, w2), (False, t, ones, w))

    def test_no_invariant(self):
        """No conserved a*ones + b*pos + W[state] modulo 2 to 8 (tools/py/bbtools/invariants.py)."""
        for mod in range(2, 9):
            self.assertEqual(conserved(blank.MACHINE, mod), [], mod)


class TestObservations(unittest.TestCase):
    def test_blocks(self):
        self.assertEqual(blank.blocks("0^2 a^13 0 a^13 0 a^18 1"), [13, 13, 18])
        self.assertEqual(blank.blocks("0^2 a 0 a^7 0 a^8 1"), [1, 7, 8])
        self.assertIsNone(blank.blocks("0^2 a^3 0^2 a^9 0 a^12 1"))

    def test_marks_follow_pairs(self):
        """At every left-end moment to 10^10 steps, the word b = 110 comes right after a block of pairs."""
        n = 0
        with open(LEFT) as f:
            for line in f:
                t = line.split()[4:]
                for i, w in enumerate(t):
                    if w == "b" or w.startswith("b^"):
                        n += 1
                        self.assertTrue(i > 0 and t[i - 1].startswith("a"), line)
        self.assertEqual(n, 67)

    def test_replay(self):
        ws = {(t, w): (n, rest) for t, j, w, n, rest in replay.walls(replay.read_events(LEFT)) if n >= 2}
        self.assertEqual(len(ws), 10)
        n, rest = ws[(277787, 257)]
        self.assertEqual(n, 29)
        lost = [257 - x for x in rest]
        self.assertEqual(lost[:8], [1, 4, 6, 10, 12, 22, 28, 38])
        # every wall loses the same amounts
        for (t, w), (n, rest) in ws.items():
            self.assertEqual([w - x for x in rest], lost[:n], t)


class TestCounter(unittest.TestCase):
    def test_predict_cases(self):
        # the four theorems of Counter.lean, on small numbers (last level rightmost; tail `0 10`)
        tail = ["0", 1]
        self.assertEqual(counter.predict([9, "1", 5, "1", 7] + tail)[0], [9, "0", 6, "1", 8] + tail)       # last2
        self.assertEqual(counter.predict([9, "0", 4, "1", 6] + tail)[0], [9, "0", 4, "0", 8] + tail)       # last1
        self.assertEqual(counter.predict([9, "1", 5, "1", 7, "0", 4, "0", 6, "0", 2, "0", 4] + tail)[0],
                         [9, "0", 6, "1", 6, "1", 5, "1", 5, "1", 3, "1", 5] + tail)                       # borrow2
        self.assertEqual(counter.predict([9, "0", 4, "1", 6, "0", 2, "0", 2] + tail)[0],
                         [9, "0", 4, "0", 6, "1", 3, "1", 3] + tail)                                       # borrow1
        self.assertEqual(counter.predict([9, "0", 4, "0", 6, "0", 2, "0", 2] + tail), (None, "left"))
        self.assertEqual(counter.predict([9, "1", 5, "1", 6, "0", 2, "0", 2] + tail), (None, "short"))

    def test_predict_on_machine(self):
        # each predicted excursion, run on the plain simulator from the predicted start, ends as predicted
        from bbtools.machine import Machine, Tape
        m = Machine.parse(M)
        for t, want in [([9, "1", 5, "1", 7, "0", 4, "0", 6, "0", 2, "0", 4], None),
                        ([9, "0", 4, "1", 6, "0", 2, "0", 2], None), ([3, "1", 1, "1", 3], None)]:
            t = t + ["0", 1]
            p, _ = counter.predict(t)
            s = counter.tape_str(t)
            tape = Tape()
            for i, ch in enumerate(s):
                tape.set(i, int(ch))
            r = Run(m, state=counter.C, tape=tape, head=len(s) - 3)
            while True:
                self.assertTrue(r.step())
                if r.state == counter.C and r.steps > 1 and [r.tape.get(r.head + i) for i in range(6)] == [0, 1, 0, 0, 0, 0]:
                    break
            got = "".join(map(str, r.tape.word(0, r.head + 1))).lstrip("0") + "0"   # the head reads `0 1`, then blank
            self.assertEqual(got, counter.tape_str(p))

    def test_blocks(self):
        import random
        import re
        rng = random.Random(1)
        for _ in range(300):
            s = "".join(rng.choice(["10", "10", "1", "0"]) for _ in range(rng.randint(1, 30)))
            want = [len(x) // 2 if len(x) > 1 else x for x in re.findall(r"(?:10)+|.", s)]
            while want and want[0] == "0":
                want.pop(0)
            while want and want[-1] == "0":
                want.pop()
            self.assertEqual(counter.blocks([int(c) for c in s]), want, s)

    def test_run_to_1e8(self):
        tally = counter.check(10 ** 8)
        self.assertEqual(tally.get("wrong", 0), 0)
        self.assertEqual(dict(tally), {"proved": 4326, "left": 108, "short": 76})


class TestTop(unittest.TestCase):
    def test_shapes_on_machine(self):
        # each proved shape, with random lengths, a random tape left of it and a random borrow, run on the plain
        # simulator from the right end: the trip ends as the shape and the counter's reset say
        import random
        from bbtools.machine import Machine, Tape
        m = Machine.parse(M)
        rng = random.Random(7)
        for st in top.load_shapes():
            sh = top.Shape(st)
            for _ in range(2):
                vals = {v: rng.randint(0, 3) for v in sh.vars}
                ctx = [rng.randint(1, 5), rng.choice("01"), rng.randint(1, 5)]
                left = top.subst(sh.lhs, vals, ctx)
                after = top.subst(sh.rhs, vals, ctx)
                if sh.turn:
                    zs = [(2 * rng.randint(1, 3), 2 * rng.randint(2, 4)) for _ in range(rng.randint(0, 2))]
                    zs.append((2 * rng.randint(1, 3), 2 * rng.randint(1, 3)))        # the last level
                    if left and isinstance(left[-1], int):
                        left[-1] += 2
                    else:
                        left.append(2)
                    for i, (g, w) in enumerate(zs):
                        left += ["0", g, "0", w]
                        after += ["1", g + 1, "1", w + 1 if i == len(zs) - 1 else w - 1]
                s = counter.tape_str(left + ["0", 1])
                tape = Tape()
                for i, ch in enumerate(s):
                    tape.set(i, int(ch))
                r = Run(m, state=counter.C, tape=tape, head=len(s) - 3)
                while True:
                    self.assertTrue(r.step())
                    if (r.state == counter.C and r.tape.get(r.head) == 0 and r.tape.get(r.head + 1) == 1
                            and not any(r.tape.word(r.head + 2, max(r.tape.hi, len(s)) + 1))):
                        break
                got = "".join(map(str, r.tape.word(min(r.tape.lo, 0), r.head - 1))).lstrip("0")
                self.assertEqual(got, counter.tape_str(after + ["0", 1])[:-3].lstrip("0"), (st, vals, ctx))

    def test_run_to_1e9(self):
        # every trip to 10^9 steps that counter.py does not cover is an instance of a family of TopFam.lean (any
        # number of blocks in the list), a wall trip of Rework.lean (any list of blocks before the copied level,
        # rework.py) or goes through a shape of Top.lean, and each ends as it says
        self.assertEqual(dict(top.check(10 ** 9)), {"family": 36, "proved": 190, "wall": 29})

    def test_rework_on_machine(self):
        # the round function of Rework.lean (py/rework.py, from the saved cases) on random lists of blocks, round
        # after round, and whole wall trips from the wall shapes with random values, against the plain simulator
        import random
        import rework
        cs = rework.cases()
        self.assertTrue(rework.check(cs, 60, seed=5))
        self.assertTrue(rework.check_walls(cs, rework.shape_lists(random.Random(5), per=2)))

    def test_families_on_machine(self):
        # each family, with random lists of 0 to 4 blocks, random values, a random tape left of it (for an `L`
        # family) and a random borrow, run on the plain simulator from the right end: the trip ends as the
        # family's end and the counter's reset say
        import random
        import family
        from bbtools.machine import Machine, Tape
        from bbtools.symtm import Ctx
        m = Machine.parse(M)
        rng = random.Random(11)
        fams = [family.Family(t) for t in family.load()]
        self.assertTrue(fams)
        for f in fams:
            vs = sorted(f.cfg.vars())
            for n in range(5):
                env = {v: rng.randint(0, 3) for v in vs}
                elems = [{p: rng.randint(0, 3) for p in f.pat.params} for _ in range(n)]
                ctx = "".join(rng.choice(["10" * rng.randint(1, 3) + "1", "10" * rng.randint(1, 3) + "0"])
                              for _ in range(2)) if any(isinstance(t, Ctx) for t in f.cfg.left) else ""
                start = family.cells(f.cfg.left, env, elems, ctx)
                end = family.cells(f.fin.left, env, elems, ctx)
                tail_after = ""
                if f.turn:
                    end = end[:-3]
                    zs = [(2 * rng.randint(1, 3), 2 * rng.randint(2, 4)) for _ in range(rng.randint(0, 2))]
                    zs.append((2 * rng.randint(1, 3), 2 * rng.randint(1, 3)))
                    start += "1010"
                    for i, (g, w) in enumerate(zs):
                        start += "0" + "10" * g + "0" + "10" * w
                        tail_after += "1" + "10" * (g + 1) + "1" + "10" * (w + 1 if i == len(zs) - 1 else w - 1)
                s = (start + "010").lstrip("0")
                want = (end + tail_after + "01").lstrip("0")
                tape = Tape()
                for i, ch in enumerate(s):
                    tape.set(i, int(ch))
                r = Run(m, state=counter.C, tape=tape, head=len(s) - 3)
                while True:
                    self.assertTrue(r.step())
                    if (r.state == counter.C and r.tape.get(r.head) == 0 and r.tape.get(r.head + 1) == 1
                            and not any(r.tape.word(r.head + 2, max(r.tape.hi, len(s)) + 1))):
                        break
                got = "".join(map(str, r.tape.word(min(r.tape.lo, 0), r.head + 1))).lstrip("0")
                self.assertEqual(got, want, (f.text, n, env, elems, ctx))

    def test_wall_match(self):
        # the round form of Wall.lean read off a symbolic tape, and the loop jump
        import wall
        from bbtools.symtm import Config, lin
        c = Config.parse("0^inf C> 0 10 (1010)^a 0 (1010)^3 0 10 10 0 0 10 (1010)^x 0 1 1 R")
        r = wall.match(c)
        self.assertEqual((r.a, r.ts, r.X), (lin("a"), [lin(2), lin(0)], 2 * lin("x") + 1))
        self.assertIsNone(wall.match(Config.parse("0^inf C> 0 10 (1010)^a 0 10 0 0 (1010)^x R")))


class TestAccel(unittest.TestCase):
    def test_bulk_is_repeated_steps(self):
        # n trips at once = n single counter steps, with the step counts of the pieces in Rules.lean
        import random
        rng = random.Random(3)
        for _ in range(200):
            levs = []
            for p in range(rng.randint(1, 5)):
                d = rng.randrange(3)
                par = 1 if d == 2 else 0
                levs.append([d, 2 * rng.randint(1, 40) + par, 2 * rng.randint(20, 400) + par])
            t = accel.with_levels([7], 1, levs)
            levs2, i0 = accel.regular(t)
            self.assertEqual(levs2, levs)
            v = accel.value(levs)
            n = accel.max_trips(levs, v)
            nl, steps = accel.bulk(levs, v, n)
            u, total = t, 0
            for _ in range(n):
                total += cost(u)
                u, why = counter.predict(u)
                self.assertIsNone(why)
            self.assertEqual(accel.with_levels(t, i0, nl), u)
            self.assertEqual(steps, total)

    def test_matches_plain_run(self):
        # every state the accelerated run passes through is a return of the plain macro run, at the same step
        plain = {s: counter.tape_str(t) for s, t in counter.returns(10 ** 9)}
        kinds = set()
        for s, trips, t, kind in accel.run(10 ** 9):
            if s > 10 ** 9:
                break
            kinds.add(kind)
            self.assertEqual(plain.get(s), counter.tape_str(t), (s, kind))
        self.assertEqual(kinds, {"bulk", "top", "proved"})

    def test_cycle_jumps(self):
        # the top trips with cycle jumps (bbtools.cycles) pass through the same returns as without them
        n = 10 ** 11
        orig = accel.concrete_trip
        try:
            accel.concrete_trip = lambda t: orig(t, accelerate=False)
            plain = {s: t for s, _, t, _ in accel.run(n)}
        finally:
            accel.concrete_trip = orig
        del accel.JUMPS[:]
        for s, _, t, _ in accel.run(n):
            if s <= n:
                self.assertEqual(plain.get(s), t, s)
        self.assertTrue(accel.JUMPS)


def cost(t):
    """Steps of one counter trip, from the pieces of Rules.lean (last2 8a+8b+26, turn2 8a+8b+19, ...)."""
    i, last, c = len(t) - 5, True, 0
    while True:
        g, w = t[i], t[i + 2]
        d = counter.DIGIT[(t[i - 1], t[i + 1])]
        if d == 2:
            return c + 4 * g + 4 * w + (18 if last else 3)
        if d == 1:
            return c + 4 * w + (16 if last else 1)
        c += 8 * g + 4 * w + (23 if last else 8)
        last = False
        i -= 4


if __name__ == "__main__":
    unittest.main(verbosity=2)
