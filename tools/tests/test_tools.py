"""Tests of the shared tools: the Python reference simulator, the C simulator against it, the symbolic prover
(against concrete runs, and through Lean when a Lean binary is installed), the parts protocol and merge, the
invariant finder, the Lean generator and the status-page builder.

usage: python3 tools/tests/test_tools.py        (from anywhere; builds the C programs into a temporary directory)
"""
import hashlib
import json
import os
import random
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
TOOLS = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(TOOLS, "py"))
sys.path.insert(0, os.path.join(TOOLS, "pages"))

from bbtools.machine import Machine, Run, run_blank, records, STATES  # noqa: E402
from bbtools import symtm, symframe, leangen, invariants, ctl, ngramcps  # noqa: E402
from bbtools.macro import MacroRun  # noqa: E402
from bbtools import cycles  # noqa: E402
from bbtools.explore import blocks, parse_words, tokenize, token_str, token_events, turns  # noqa: E402
import merge_parts  # noqa: E402
import build_status  # noqa: E402
import explainer_status  # noqa: E402
import build_explainer  # noqa: E402
import syncpair  # noqa: E402

THIS = "1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB"
HOLDOUT = "1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE"
CHAMPIONS = {   # machine: steps to halt from blank tape, bbchallenge count
    "1RB1LB_1LA1RZ": 6,
    "1RB1RZ_1LB0RC_1LC1LA": 21,
    "1RB1LB_1LA0LC_1RZ1LD_1RD0RA": 107,
}
BB5 = "1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA"
LOOP2 = "1RB0LB_0LA---"     # never halts from blank tape, which tools/lean/Test/Examples.lean proves with a CTL

BUILD = tempfile.mkdtemp(prefix="bbtools-test-")


def cc(name):
    out = os.path.join(BUILD, name)
    if not os.path.exists(out):
        subprocess.run(["gcc", "-O2", "-Wall", "-Wextra", "-Werror", "-o", out, os.path.join(TOOLS, "c", name + ".c")],
                       check=True)
    return out


def random_machine(rng, n):
    groups = []
    halt = (rng.randrange(n), rng.randrange(2))
    for s in range(n):
        g = ""
        for y in (0, 1):
            g += "---" if (s, y) == halt else f"{rng.randrange(2)}{rng.choice('LR')}{STATES[rng.randrange(n)]}"
        groups.append(g)
    return "_".join(groups)


class TestMachine(unittest.TestCase):
    def test_parse(self):
        m = Machine.parse(THIS)
        self.assertEqual(m.n, 6)
        self.assertEqual(m.table[0][0], (1, 1, 1))      # A0 -> 1RB
        self.assertEqual(m.table[3][0], None)           # D0 -> ---
        self.assertEqual(m.halting_transitions(), ["D0"])
        self.assertEqual(Machine.parse("1RB1LB_1LA1RZ").halting_transitions(), ["B1"])
        for bad in ["1RB", "1RB1LB_1LA1R", "2RB1LB_1LA1RZ", "1XB1LB_1LA1RZ"]:
            with self.assertRaises(ValueError):
                Machine.parse(bad)

    def test_champions(self):
        for text, steps in CHAMPIONS.items():
            h, t, _ = run_blank(text, 10 ** 6)
            self.assertTrue(h, text)
            self.assertEqual(t, steps, text)

    def test_blocks(self):
        self.assertEqual(blocks([1, 1, 0, 1, 0, 0]), [(2, 1), (1, 2)])
        self.assertEqual(blocks([0, 1]), [(0, 1), (1, 0)])

    def test_tokens(self):
        words = parse_words("a=10,b=110")
        self.assertEqual([w[0] for w in words], ["b", "a"])
        cells = [0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1]
        self.assertEqual(token_str(tokenize(cells, words)), "0^2 a^2 b 0 a 1")
        for bad in ("a=12", "0=10", "a="):
            with self.assertRaises(ValueError):
                parse_words(bad)
        # reading the tokens back gives the cells
        rng = random.Random(3)
        for _ in range(200):
            cells = [rng.randrange(2) for _ in range(rng.randrange(30))]
            back = []
            for t, k in tokenize(cells, words):
                back += (list(dict(words)[t]) if t in dict(words) else [int(t)]) * k
            self.assertEqual(back, cells)

    def test_turns(self):
        m = Machine.parse(THIS)
        ts = list(turns(m, 0, 2000))
        self.assertTrue(ts)
        r = Run(m)
        last = None
        for t, s, pos, d in ts:
            while r.steps < t - 1:
                r.step()
            h, st = r.head, r.state
            r.step()
            self.assertEqual((r.steps, st, h - r.tape.lo, ">" if r.head > h else "<"), (t, s, pos, d))
            self.assertNotEqual(d, last)
            last = d


class TestC(unittest.TestCase):
    def tmrun(self, *args):
        return subprocess.run([cc("tmrun")] + [str(a) for a in args], check=True, capture_output=True,
                              text=True).stdout

    def test_champions(self):
        for text, steps in CHAMPIONS.items():
            self.assertEqual(self.tmrun(text, 10 ** 6).split()[:2], ["halted", str(steps)])
        out = self.tmrun(BB5, 10 ** 8).split()
        self.assertEqual(out[:2], ["halted", "47176870"])
        self.assertEqual(out[2], "4097")    # the 1s before the halting transition, which writes the 4,098th

    def test_random_against_python(self):
        rng = random.Random(1)
        for _ in range(150):
            text = random_machine(rng, rng.randrange(2, 7))
            r = Run(Machine.parse(text))
            h = r.run(3000)
            out = self.tmrun(text, 3000).split()
            self.assertEqual(out, ["halted" if h else "running", str(r.steps), str(r.ones())], text)

    def test_records_against_python(self):
        out = self.tmrun(THIS, 20000, "records", 60).splitlines()[:-1]
        py = [f"{t} {side} {r.tape.hi - r.tape.lo} {r.config_str()}" for t, side, r in records(Machine.parse(THIS), 20000)]
        self.assertEqual(out, py[:60])


    def test_tokrun_against_python(self):
        for text, words in ((THIS, "a=10,b=110"), (HOLDOUT, "x=1110,y=10")):
            out = subprocess.run([cc("tokrun"), text, "200000", words, "LR", "80"], check=True, capture_output=True,
                                 text=True).stdout.splitlines()
            ws, py = parse_words(words), []
            for r, side in token_events(Machine.parse(text), 200000, ws):
                if len(py) == 80:
                    break
                py.append(f"{r.steps} HALT" if side == "HALT" else
                          f"{r.steps} {side} {r.tape.hi - r.tape.lo} {STATES[r.state]} {token_str(tokenize(r.tape.word(), ws))}")
            self.assertEqual(out, py, text)
        for text, steps in CHAMPIONS.items():
            out = subprocess.run([cc("tokrun"), text, "1000", "a=10"], check=True, capture_output=True,
                                 text=True).stdout.splitlines()
            self.assertEqual(out[-1], f"{steps} HALT")


class TestMacro(unittest.TestCase):
    def test_champions(self):
        for m, n in CHAMPIONS.items():
            for k in (1, 2, 3, 5):
                r = MacroRun(m, k).run(10 ** 6)
                self.assertTrue(r.halted, (m, k))
                self.assertEqual(r.steps, n, (m, k))

    def test_bb5(self):
        r = MacroRun(BB5, 6).run(10 ** 9)
        self.assertTrue(r.halted)
        self.assertEqual(r.steps, 47176870)

    def test_against_plain(self):
        # the tape, head, state and step count after each macro step equal the plain simulator's at that step
        for m in (THIS, HOLDOUT, "1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE---"):
            for k in (2, 3, 4):
                r, p = MacroRun(m, k), Run(Machine.parse(m))
                for _ in range(1500):
                    if not r.step():
                        break
                    while p.steps < r.steps:
                        p.step()
                    self.assertEqual((p.steps, p.state, p.head), (r.steps, r.state, r.head()), (m, k))
                    cells = r.cells()
                    for i in range(min(cells.keys() | {p.tape.lo}), max(cells.keys() | {p.tape.hi}) + 1):
                        self.assertEqual(cells.get(i, 0), p.tape.get(i), (m, k, r.steps, i))

    def test_runs_compress(self):
        # 1RB1RF_1LC0LB's sweeps cross whole runs of pairs: a million steps in about ten thousand macro steps
        r = MacroRun("1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE---", 4).run(10 ** 6)
        self.assertLess(r.msteps, 20000)


BB6_1RF = "1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE---"
BOUNCER = "1LB1RA_1RA1LB"     # a block of 1s growing by one cell at each end per sweep
EATER = "0RB1RA_0RB0LC_0LC1LD_1RA1LD"   # on 1^a 0^z 1^b: a and z grow by one, b shrinks by one per sweep


def eater_run(b):
    """EATER from 0^inf A> 1 0 1^b 0^inf (a macro run with blocks of one cell)."""
    r = MacroRun(EATER, 1)
    r.right = [[(0,), 1], [(1,), b], [(0,), 1], [(1,), 1]]
    return r


def lean_env():
    lean = os.environ.get("LEAN") or shutil.which("lean")
    lib = os.environ.get("LEANLIB") or os.path.join(os.path.dirname(os.path.dirname(os.path.realpath(lean))),
                                                    "lib", "lean")
    return lean, lib


def check_rules_lean(test, machine, theorems):
    """Compile `theorems` (Lean texts from symtm.prove) against the machine's generated definition."""
    lean, lib = lean_env()
    subprocess.run([os.path.join(TOOLS, "lean", "check.sh")], check=True, capture_output=True,
                   env=dict(os.environ, LEAN=lean, LEANLIB=lib))
    d = tempfile.mkdtemp(dir=BUILD)
    with open(os.path.join(d, "Mach.lean"), "w") as f:
        f.write(leangen.machine_lean(machine, "Mach"))
    with open(os.path.join(d, "Rules.lean"), "w") as f:
        f.write(symtm.rules_file("Mach", "Mach", theorems, "test rules"))
    env = dict(os.environ, LEAN_PATH=f"{lib}:{os.path.join(TOOLS, 'lean', 'out')}:{d}")
    subprocess.run([lean, "Mach.lean", "-o", "Mach.olean"], cwd=d, check=True, env=env, capture_output=True)
    r = subprocess.run([lean, "Rules.lean"], cwd=d, env=env, capture_output=True, text=True)
    test.assertEqual(r.returncode, 0, r.stdout + r.stderr)


class TestCycles(unittest.TestCase):
    """The cycle accelerator against plain macro runs: after every jump the stacks, head position, state and step
    count are those of the macro machine run without jumps."""

    @staticmethod
    def accelerated(run, steps, **kw):
        a = cycles.Accelerator(run, **kw)
        ends = []
        jump = a.jump

        def recording(limit=None):
            n = jump(limit)
            if n:
                ends.append(cycles.snapshot(a.run_))
            return n
        a.jump = recording
        a.run(steps)
        return a, ends

    def check_against_plain(self, machine, k, steps, min_jumps, start=None):
        start = start or (lambda: MacroRun(machine, k))
        a, ends = self.accelerated(start(), steps)
        self.assertGreaterEqual(len(ends), min_jumps)
        p = start()
        for e in ends:
            while p.steps < e.steps and p.step():
                pass
            self.assertEqual(cycles.snapshot(p), e, (machine, k, e.steps))
        while p.steps < steps and p.step():
            pass
        self.assertEqual(cycles.snapshot(p), cycles.snapshot(a.run_))
        return a

    def test_detect(self):
        w, v = (1, 0), (0, 1)
        s = [cycles.Snap(100 + 10 * i + i * i, -4 * i, 1, -1, ((w, 5 + 2 * i), (v, 3)), ((w, 40 - i),))
             for i in range(3)]
        c = cycles.detect(s)
        self.assertEqual(c.delta, (2, 0, -1))
        self.assertEqual(c.dpos, -4)
        self.assertEqual(c.dsteps, (11, 13))
        self.assertIsNone(cycles.detect([s[0], s[1], s[1]]))      # not linear
        t = cycles.Snap(0, 0, 1, -1, ((v, 5),), ((w, 40),))
        self.assertIsNone(cycles.detect([s[0], t]))                 # another shape

    def test_bb6_1rf_against_macro(self):
        # walls eaten and blocks grown at the left end; many jumps, each one checked
        a = self.check_against_plain(BB6_1RF, 4, 3 * 10 ** 8, 10)
        self.assertGreater(sum(n for _, n, _, _ in a.jumps), 1000)

    def test_bouncer_against_macro(self):
        # nothing shrinks: the jumps are bounded only by the step limit, and land on it exactly where they can
        for k in (1, 2, 3):
            a = self.check_against_plain(BOUNCER, k, 10 ** 7, 1)
            self.assertGreater(a.jumps[0][1], 500)

    def test_eater_wall(self):
        # the wall 1^b is eaten one cell per sweep: one jump, which stops with the wall still `margin` above what
        # the rule needs; then the machine leaves to the right in blank tape, another jump
        a = self.check_against_plain(EATER, 1, 3 * 10 ** 6, 2, start=lambda: eater_run(1000))
        before, n, after, name = a.jumps[0]
        rule = a.rules[0]
        self.assertEqual(rule.delta, (-1, 1, 1))
        self.assertEqual(str(rule.steps), "2*n1+2*n2+15")
        p = eater_run(1000).run(after)
        wall = p.right[1][1]
        self.assertEqual(wall, rule.spec[0][2] + 2)        # offset + margin
        self.assertGreater(n, 900)

    def test_rules_hold_concretely(self):
        """Each rule, its variables filled in with values unlike the sample's, is a true statement (plain run)."""
        a, _ = self.accelerated(MacroRun(BB6_1RF, 4), 3 * 10 ** 7)
        b = cycles.Accelerator(MacroRun(BOUNCER, 2)).run(10 ** 5)
        c = cycles.Accelerator(eater_run(300)).run(10 ** 6)
        cases = [(BB6_1RF, r) for r in a.rules[:6]] + [(BOUNCER, r) for r in b.rules] + [(EATER, r) for r in c.rules]
        self.assertGreater(len(cases), 4)
        rng = random.Random(5)
        for text, rule in cases:
            m = Machine.parse(text)
            for _ in range(3):
                env = {v: rng.randrange(0, 12) for v in rule.start.vars()}
                start, end = rule.start, rule.end
                cells, head = TestSymbolic.concretize(start, env, {})
                ecells, ehead = TestSymbolic.concretize(end, env, {})
                r = Run(m, state=start.state)
                for i, x in enumerate(cells):
                    r.tape.set(i, x)
                r.head = head
                n = rule.steps.subs(env)
                for _ in range(n):
                    self.assertTrue(r.step())
                self.assertEqual(r.state, end.state)
                off = r.head - ehead
                lo, hi = min(off, r.tape.lo), max(off + len(ecells), r.tape.hi + 1)
                self.assertEqual([r.tape.get(i) for i in range(lo, hi)],
                                 [ecells[i - off] if 0 <= i - off < len(ecells) else 0 for i in range(lo, hi)],
                                 (rule.name, env))

    def test_margin(self):
        # after every jump each shrinking count is still `margin` above what its rule needs
        a, ends = self.accelerated(MacroRun(BB6_1RF, 4), 10 ** 8, margin=5)
        by_name = {r.name: r for r in a.rules}
        self.assertGreater(len(ends), 5)
        for (_, n, _, name), e in zip(a.jumps, ends):
            rule = by_name[name]
            self.assertGreaterEqual(n, 2)
            shrinking = [(sp, c) for sp, c, d in zip(rule.spec, e.counts(), rule.delta) if d < 0]
            self.assertTrue(shrinking)
            for sp, c in shrinking:
                self.assertEqual(sp[0], "var")
                self.assertGreaterEqual(c, sp[2] + 5)

    @unittest.skipUnless(shutil.which("lean") or os.environ.get("LEAN"), "no Lean installed")
    def test_lean_checks(self):
        """The cycle rules (shift rules, re-bracketings, a step count linear in the variables) compile in Lean."""
        a, _ = self.accelerated(MacroRun(BB6_1RF, 4), 10 ** 6)
        self.assertTrue(any("rep_rotate" in r.lean for r in a.rules[:3]))
        check_rules_lean(self, BB6_1RF, [r.lean for r in a.rules[:3]])
        b = cycles.Accelerator(MacroRun(BOUNCER, 2)).run(10 ** 5)
        check_rules_lean(self, BOUNCER, [r.lean for r in b.rules])
        c = cycles.Accelerator(eater_run(300)).run(10 ** 6)
        check_rules_lean(self, EATER, [r.lean for r in c.rules])


class TestParts(unittest.TestCase):
    def test_split_and_merge(self):
        ws = cc("windowscan")
        run_parts = os.path.join(TOOLS, "c", "run_parts.sh")
        d = tempfile.mkdtemp(dir=BUILD)
        args = [HOLDOUT, "A", "12", "500"]
        whole = subprocess.run([ws] + args, check=True, capture_output=True, text=True).stdout
        with open(os.path.join(d, "whole.txt"), "w") as f:
            f.write(whole)
        subprocess.run([run_parts, "5", "3", os.path.join(d, "p")] + [ws] + args, check=True, capture_output=True)
        parts = sorted(os.path.join(d, "p", f) for f in os.listdir(os.path.join(d, "p")) if f.endswith(".txt")
                       and f.startswith("part_"))
        self.assertEqual(len(parts), 5)
        merged, problems = merge_parts.merge(parts)
        self.assertEqual(problems, [])
        one, problems1 = merge_parts.merge([os.path.join(d, "whole.txt")])
        self.assertEqual(problems1, [])
        strip = lambda ls: sorted(x for x in ls if not x.startswith("done") and not x.startswith("event"))
        self.assertEqual(strip(merged), strip(one))
        self.assertEqual(sorted(x for x in merged if x.startswith("event")),
                         sorted(x for x in one if x.startswith("event")))
        self.assertIn("sum words 4096", merged)
        # a missing part and an unfinished part are refused
        _, p2 = merge_parts.merge(parts[1:])
        self.assertTrue(any("missing" in x for x in p2))
        bad = os.path.join(d, "unfinished.txt")
        with open(parts[0]) as f, open(bad, "w") as g:
            g.write("".join(l for l in f if not l.startswith("done")))
        _, p3 = merge_parts.merge([bad] + parts[1:])
        self.assertTrue(any("no done line" in x for x in p3))
        # rerunning skips finished parts
        with open(os.path.join(d, "p", "times.txt")) as f:
            before = f.read()
        subprocess.run([run_parts, "5", "3", os.path.join(d, "p")] + [ws] + args, check=True, capture_output=True)
        with open(os.path.join(d, "p", "times.txt")) as f:
            self.assertEqual(f.read(), before)


class TestSymFrame(unittest.TestCase):
    """The framed proofs (symframe.py): the same runs as symtm.prove, the pieces stated once in a shared library."""

    def test_same_run(self):
        lib = symframe.Library("p_")
        for name, a, b in TestSymbolic.RULES:
            t, fin = symframe.prove_framed(THIS, name, a, b, lib=lib)
            self.assertEqual(str(fin), str(symtm.prove(THIS, name, a, b)[1]))
            self.assertIn("steps_seq trans" if "steps_seq" in t else "exact steps_congr", t)
        self.assertTrue(lib.items)

    @unittest.skipUnless(shutil.which("lean") or os.environ.get("LEAN"), "no Lean installed")
    def test_lean_checks(self):
        lib = symframe.Library("p_")
        ths = [symframe.prove_framed(THIS, n, a, b, lib=lib, max_seg=3)[0] for n, a, b in TestSymbolic.RULES]
        check_rules_lean(self, THIS, [lib.text()] + ths)


class TestSymbolic(unittest.TestCase):
    RULES = [   # (name, start, end) for THIS machine
        ("a_sweep", "L A> 1^n R", "L 1^n A> R"),
        ("b_sweep", "L 0 1^n B> 1 R", "L B> 0 1 1^n R"),
    ]

    def test_concrete_agrees(self):
        """Symbolic steps on concrete tokens agree with the reference simulator."""
        rng = random.Random(2)
        for _ in range(60):
            text = random_machine(rng, rng.randrange(2, 7))
            m = Machine.parse(text)
            c = symtm.Config([symtm.Blank()], 0, [symtm.Blank()])
            r = Run(m)
            for _ in range(300):
                try:
                    symtm.step(m, c)
                except symtm.Halted:
                    self.assertFalse(r.step())
                    break
                self.assertTrue(r.step())
                cells = [x for x in c.left if isinstance(x, int)] + [x for x in c.right if isinstance(x, int)]
                pos = len([x for x in c.left if isinstance(x, int)])
                lo = r.head - pos
                self.assertEqual(cells, [r.tape.get(p) for p in range(lo, lo + len(cells))])
                self.assertEqual(c.state, r.state)

    def test_rules_hold_concretely(self):
        """Each proved rule, with its variables and contexts filled in, is a true statement about the machine."""
        m = Machine.parse(THIS)
        rng = random.Random(3)
        for name, a, b in self.RULES:
            _, fin = symtm.prove(m, name, a, b)
            start = symtm.Config.parse(a)
            for n in range(0, 6):
                env = {"n": n}
                ctx = {"L": [rng.randrange(2) for _ in range(5)], "R": [rng.randrange(2) for _ in range(5)]}
                s_cells, s_head = self.concretize(start, env, ctx)
                e_cells, e_head = self.concretize(fin, env, ctx)
                r = Run(m, state=start.state)
                for i, x in enumerate(s_cells):
                    r.tape.set(i, x)
                r.head = s_head
                for _ in range(fin.steps.subs(env)):
                    self.assertTrue(r.step())
                self.assertEqual(r.state, fin.state)
                self.assertEqual(len(e_cells), len(s_cells))
                self.assertEqual(r.head, e_head)
                self.assertEqual([r.tape.get(i) for i in range(len(e_cells))], e_cells)

    @staticmethod
    def concretize(c, env, ctx):
        def side(tks):
            out = []
            for t in tks:
                if isinstance(t, int):
                    out.append(t)
                elif isinstance(t, symtm.Rep):
                    out.extend(list(t.word) * t.n.subs(env))
                elif isinstance(t, symtm.Ctx):
                    out.extend(ctx[t.name])
            return out
        left, right = side(c.left), side(c.right)
        return left + right, len(left)

    def test_lean_text(self):
        t, fin = symtm.prove(THIS, "b_sweep", "L 0 1^n B> 1 R", "L B> 0 1 1^n R")
        self.assertIn("cross_l trans", t)
        self.assertEqual(str(fin), "L B> 0 1 (1)^n R")
        with self.assertRaises(symtm.ProofError):
            symtm.prove(THIS, "bad", "L 0 1^n+1 A> 0 R", "L 0 1^n+1 A> 0 R")     # reads R

    @unittest.skipUnless(shutil.which("lean") or os.environ.get("LEAN"), "no Lean installed")
    def test_lean_checks(self):
        """The generated rules compile in Lean (Lean is the judge of the proofs)."""
        lean = os.environ.get("LEAN") or shutil.which("lean")
        lib = os.environ.get("LEANLIB") or os.path.join(os.path.dirname(os.path.dirname(os.path.realpath(lean))),
                                                        "lib", "lean")
        subprocess.run([os.path.join(TOOLS, "lean", "check.sh")], check=True, capture_output=True,
                       env=dict(os.environ, LEAN=lean, LEANLIB=lib))
        d = tempfile.mkdtemp(dir=BUILD)
        with open(os.path.join(d, "Mach.lean"), "w") as f:
            f.write(leangen.machine_lean(THIS, "Mach"))
        ths = [symtm.prove(THIS, n, a, b)[0] for n, a, b in self.RULES]
        with open(os.path.join(d, "Rules.lean"), "w") as f:
            f.write(symtm.rules_file("Mach", "Mach", ths, "test rules"))
        env = dict(os.environ, LEAN_PATH=f"{lib}:{os.path.join(TOOLS, 'lean', 'out')}:{d}")
        subprocess.run([lean, "Mach.lean", "-o", "Mach.olean"], cwd=d, check=True, env=env, capture_output=True)
        r = subprocess.run([lean, "Rules.lean"], cwd=d, env=env, capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)


class TestInvariants(unittest.TestCase):
    def test_holdout_mod3(self):
        """The holdout's mod-3 count of 1s with a state weight (bb6-holdout's notes) is found."""
        m = Machine.parse(HOLDOUT)
        sols = invariants.primitive(invariants.conserved(m, 3), 3)
        self.assertTrue(any(a != 0 and b == 0 for a, b, _ in sols))

    def test_conserved_along_runs(self):
        rng = random.Random(4)
        checked = 0
        for _ in range(400):
            text = random_machine(rng, rng.randrange(2, 5))
            m = Machine.parse(text)
            for mod in (2, 3, 4):
                for a, b, W in invariants.conserved(m, mod):
                    r = Run(m)
                    q0 = W[0] % mod
                    for _ in range(200):
                        if not r.step():
                            break
                        self.assertEqual((a * r.ones() + b * r.head + W[r.state]) % mod, q0, text)
                    checked += 1
        self.assertGreater(checked, 10)


class TestLeanGen(unittest.TestCase):
    def test_round_trip(self):
        norm = lambda t: "_".join("".join("---" if x is None else f"{x[0]}{'R' if x[1] == 1 else 'L'}{STATES[x[2]]}"
                                          for x in row) for row in Machine.parse(t).table)
        for text in [THIS, HOLDOUT, BB5] + list(CHAMPIONS):
            self.assertEqual(leangen.parse_lean_table(leangen.machine_lean(text, "X")), norm(text))

    def test_committed_files_current(self):
        for name, text in [("BB2", "1RB1LB_1LA1RZ"), ("BB4", "1RB1LB_1LA0LC_1RZ1LD_1RD0RA"), ("Loop2", LOOP2)]:
            with open(os.path.join(TOOLS, "lean", "Test", name + ".lean")) as f:
                self.assertEqual(f.read(), leangen.machine_lean(text, "Test." + name))


class TestCTL(unittest.TestCase):
    def test_random_against_runs(self):
        """The set found for random machines passes the closure check, holds every configuration of the run, and
        lists every halt that happens."""
        rng = random.Random(7)
        done = 0
        for _ in range(200):
            text = random_machine(rng, rng.choice([2, 3, 4]))
            try:
                AL, AR, S = ctl.search(text, 2, max_rounds=30)
            except RuntimeError:
                continue
            self.assertTrue(ctl.check(text, AL, AR, S), text)
            halts = {(s, ql, qr) for (s, ql, qr, _, _) in ctl.halting(text, AR, S)}
            m = Machine.parse(text)
            r = Run(m)
            for _ in range(300):
                t, h = r.tape, r.head
                left = [t.get(p) for p in range(h - 1, t.lo - 1, -1)]
                right = [t.get(p) for p in range(h, t.hi + 1)]
                a = ctl.abstract(AL, AR, r.state, left, right)
                self.assertIn(a, S, text)
                if not r.step():
                    self.assertIn(a, halts, text)
                    break
            done += 1
        self.assertGreater(done, 50)

    def test_loop2_no_halt(self):
        AL, AR, S = ctl.search(LOOP2, 2)
        self.assertTrue(ctl.check(LOOP2, AL, AR, S))
        self.assertEqual(ctl.halting(LOOP2, AR, S), [])

    def test_committed_cert_current(self):
        with open(os.path.join(TOOLS, "lean", "Test", "Loop2Cert.lean")) as f:
            self.assertEqual(f.read(), ctl.lean_file(LOOP2, 2, "Test.Loop2", "Test.Loop2"))


class TestNGramCPS(unittest.TestCase):
    """tools/c/ngramcps.c against the literal transcription of the paper's Algorithm 2 (bbtools/ngramcps.py), the
    paper's examples, and tools/c/ngramtwin.c on the holdout."""

    @staticmethod
    def c(text, nl, nr, *opt):
        out = subprocess.run([cc("ngramcps"), text, str(nl), str(nr)] + list(opt), check=True, capture_output=True,
                             text=True).stdout
        return dict(line.split(" ", 1) for line in out.splitlines() if " " in line)

    def test_random_against_reference(self):
        rng = random.Random(3)
        seen = set()
        for i in range(160):
            text = random_machine(rng, rng.choice([3, 4, 5]))
            nl, nr = rng.randint(1, 4), rng.randint(1, 4)
            mode = ["plain", "h1", "h2", "lru"][i % 4]
            kw = {"plain": {}, "h1": {"history": 1}, "h2": {"history": 2}, "lru": {"lru": True}}[mode]
            opt = {"plain": [], "h1": ["-H", "1"], "h2": ["-H", "2"], "lru": ["-U"]}[mode]
            r, C = ngramcps.ngram_cps(text, nl, nr, limit=200000, **kw)
            if r == "LIMIT":
                continue
            d = self.c(text, nl, nr, *opt)
            self.assertEqual(d["result"], r, (text, nl, nr, mode))
            if r == "NONHALT":
                self.assertEqual(int(d["configs"]), len(C), (text, nl, nr, mode))
            seen.add((mode, r))
        self.assertEqual(len(seen), 8)

    def test_paper_examples(self):
        # Figure 7: a translated cycler that NGramCPS decides; Figure 8: decided by the LRU augmentation only
        self.assertEqual(self.c("1RB0LE_1LC0RD_---1LD_1RE0LA_1LA0RE", 2, 2)["result"], "NONHALT")
        fig8 = "1RB0RA_1LC---_1RC1LD_0LE1RA_0LC0LE"
        self.assertEqual(self.c(fig8, 2, 2)["result"], "UNKNOWN")
        self.assertEqual(self.c(fig8, 2, 2, "-H", "2")["result"], "UNKNOWN")
        self.assertEqual(self.c(fig8, 2, 2, "-U")["result"], "NONHALT")
        self.assertEqual(self.c(BB5, 3, 3)["result"], "UNKNOWN")

    def test_holdout_derivation(self):
        """On the holdout every width fails; the derivation ends with the packet meeting a block (A1 E1 B0 C1 D1)."""
        path = os.path.join(BUILD, "deriv.txt")
        d = self.c(HOLDOUT, 12, 12, "-w", path, "-s", "200000")
        self.assertEqual(d["result"], "UNKNOWN")
        with open(path) as f:
            rows = [line.split() for line in f if not line.startswith("#")]
        self.assertEqual(int(d["derivation_length"]), len(rows) - 1)
        self.assertEqual("".join(r[2][0] for r in rows[-5:]), "AEBCD")
        self.assertTrue(rows[-5][1].endswith("011") and rows[-5][3].startswith("1"))
        self.assertEqual(rows[0][4], "real")
        self.assertIn("UNREAL", [r[4] for r in rows])

    def test_twin(self):
        sys.path.insert(0, os.path.join(TOOLS, "..", "bb6-holdout", "ngramcps"))
        import twin
        cells, head, state = twin.round_start([("W", 743), ("W", 1802), ("W", 3319)], 3326)
        path = os.path.join(BUILD, "twin.tape")
        twin.write_tape(path, cells, head, state)

        def run(n, steps, hsteps):
            out = subprocess.run([cc("ngramtwin"), HOLDOUT, str(n), str(n), path, str(steps), str(hsteps)],
                                 check=True, capture_output=True, text=True).stdout
            return dict(line.split(" ", 1) for line in out.splitlines() if " " in line)
        d = run(4, 10 ** 7, 2 * 10 ** 7)
        self.assertEqual((d["verdict"], d["twin_steps"]), ("CERTIFIED", "11362210"))   # pass_r6_halt_example
        self.assertEqual(run(4, 10 ** 7, 10 ** 6)["verdict"], "NOT_CERTIFIED")     # not run to its halt
        self.assertEqual(run(40, 10 ** 7, 2 * 10 ** 7)["verdict"], "NOT_CERTIFIED")  # sees the wall 6 from the end
        # a configuration of the run from blank tape is covered at every width, by a run that has passed it
        r = Run(Machine.parse(HOLDOUT))
        r.run(5000)
        t = r.tape
        cells = "".join(str(t.get(p)) for p in range(t.lo, t.hi + 1))
        twin.write_tape(path, cells, r.head - t.lo, STATES[r.state])
        for n in (1, 7, 30):
            self.assertEqual(run(n, 5001, 10)["covered"], "1")


class TestStatusPage(unittest.TestCase):
    def test_build(self):
        spec = {"title": "T", "machine": THIS, "claims": [
            {"level": "kernel", "title": "k", "text": "a"}, {"level": "open", "title": "o", "text": "b"}]}
        page = build_status.build(spec)
        self.assertIn("t-kernel", page)
        self.assertIn('class="card open"', page)
        with self.assertRaises(ValueError):
            build_status.build({"title": "T", "machine": THIS, "claims": [{"level": "proved", "title": "x", "text": ""}]})

    def test_explainer_status(self):
        spec = {"asof": "now", "claims": [{"level": "kernel", "title": "k", "text": "a</b>", "where": "w"}]}
        page = '<p>x</p>\n<script type="application/json" id="status-data">\nold\n</script>\n'
        out = explainer_status.build(page, spec)
        self.assertIn('"title": "k"', out)
        self.assertNotIn("</b>", out)
        self.assertEqual(explainer_status.build(out, spec), out)
        with self.assertRaises(ValueError):
            explainer_status.build("<p>no block</p>", spec)


class TestExplainerPage(unittest.TestCase):
    """tools/pages/build_explainer.py: the page builds, and its engine, run in Node, agrees with bbtools."""

    def test_build(self):
        spec = {"title": "T", "machine": THIS, "claims": [{"level": "kernel", "title": "k", "text": "a"}],
                "explainer": {"sections": [{"id": "x", "heading": "Extra", "html": ["<p>one</p>", "<p>two</p>"]}]}}
        page = build_explainer.build(spec)
        self.assertIn('<script id="engine">', page)
        self.assertIn('<section id="x">', page)
        self.assertIn("<p>one</p>\n<p>two</p>", page)
        with self.assertRaises(ValueError):
            build_explainer.build({"title": "T", "machine": THIS, "claims": [{"level": "proved", "title": "x", "text": ""}]})

    def test_halt_analysis(self):
        self.assertEqual(build_explainer.halt_analysis(Machine.parse(BB5)),
                         [("E0", [("C1", 0, "L", "0 C>1")])])
        self.assertEqual(build_explainer.halt_analysis(Machine.parse("1RB0LF_1RC0LB_1RD1RB_1RE1RF_1LA---_0RC1LA")),
                         [("E1", [("D0", 1, "R", "D>0 1")])])

    def test_xs_widgets(self):
        sec = {"id": "x", "heading": "X", "html": "<p>x</p>", "widget": "sweep"}
        spec = {"title": "T", "machine": THIS, "explainer": {"sections": [sec], "xs": {"state": "C", "off": 0, "cost": 12}}}
        page = build_explainer.build(spec)
        self.assertIn('data-xs="sweep"', page)
        self.assertIn('<script id="xs-engine">', page)
        self.assertNotIn('<script id="xs-engine">', build_explainer.build({"title": "T", "machine": THIS}))
        with self.assertRaises(ValueError):
            build_explainer.build({"title": "T", "machine": THIS, "explainer": {"sections": [sec]}})

    @unittest.skipUnless(shutil.which("node"), "node is not installed")
    def test_xs_engine(self):
        """The XOR-sweep engine of the F08 pages: at each of the first 2,000 turns at the right end of the real
        machine, the sweep rule gives the next word and 4 d + cost steps, the zone orbit is the real machine, and at
        Lean's zone step 3 * 10^7 (the zone orbit here skips Lean's few turns that are not at the right end, so it is
        compared at the same machine step) it is in the state that lean/DumpState.lean prints (t, n, md5 of Z)."""
        ms = [["1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA", 2, 0, 12, 1798864615611754, 29990528, "d9b3638b0e41fea64f76c522e742e492"],
              ["1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA", 2, 0, 12, 1798978906793042, 29991481, "3d997df242dc51c85718f48ff7a4bad3"],
              ["1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA", 3, -1, 14, 1752176669723814, 29596028, "f79c5015525dd3794af7d025a46570bd"],
              ["1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB", 3, 0, 12, 1786522819770046, 29887259, "6b3349565dee546e40c25955bcc79af3"]]
        path = os.path.join(BUILD, "xs.js")
        with open(path, "w") as f:
            f.write(build_explainer.ENGINE + build_explainer.XS_ENGINE)
            f.write("const MS = %s;\n" % json.dumps(ms))
            f.write(r"""
console.log(JSON.stringify(MS.map(([t, st, off, cost, T]) => {
  const m = BB.parse(t), xc = { state: st, off: off }, r = new BB.Run(m), Z = new BB.Zone(m, xc, cost);
  let w = BB.xsNext(r, xc), bad = 0, sweeps = 0;
  if (Z.t !== r.steps) bad++;
  for (let k = 0; k < 2000; k++) {
    const s = BB.xsSweep(w), s0 = r.steps, w2 = BB.xsNext(r, xc, 1e8);
    if (s.kind === "ok") { sweeps++; if (s.x.concat([1, 1]).join("") !== w2.join("") || r.steps - s0 !== 4 * s.d + cost) bad++; }
    const q = BB.xsRun(m, xc, w), w3 = BB.xsNext(q, xc, 1e8);
    if (w3.join("") !== w2.join("") || q.steps !== r.steps - s0) bad++;
    Z.step();
    if (Z.t !== r.steps || Z.word().join("") !== w2.join("")) bad++;
    w = w2;
  }
  while (Z.t < T && !Z.halted) Z.step();
  return [bad, sweeps, Z.t, Z.n, Z.z.slice().reverse().join("")];
})));
""")
        got = json.loads(subprocess.run(["node", path], check=True, capture_output=True, text=True).stdout)
        for m, (bad, sweeps, t, n, z) in zip(ms, got):
            self.assertEqual(bad, 0, m[0])
            self.assertGreater(sweeps, 1980, m[0])
            self.assertEqual([t, n, hashlib.md5(z.encode()).hexdigest()], m[4:], m[0])

    @unittest.skipUnless(shutil.which("node"), "node is not installed")
    def test_engine_against_python(self):
        rng = random.Random(7)
        machines = [BB5, THIS, HOLDOUT, LOOP2] + [random_machine(rng, rng.randint(2, 5)) for _ in range(40)]
        steps = [0, 1, 2, 7, 50, 333, 2000]
        path = os.path.join(BUILD, "engine.js")
        with open(path, "w") as f:
            f.write(build_explainer.ENGINE)
            f.write("const MS = %s, ST = %s;\n" % (json.dumps(machines), json.dumps(steps)))
            f.write("console.log(JSON.stringify(MS.map(t => { const m = BB.parse(t);"
                    " return { at: ST.map(n => { const r = new BB.Run(m); const h = r.run(n);"
                    " return [h, r.steps, r.ones(), r.configStr()]; }),"
                    " recs: BB.records(m, 3000, 60).records }; })));\n")
        got = json.loads(subprocess.run(["node", path], check=True, capture_output=True, text=True).stdout)
        for t, g in zip(machines, got):
            m = Machine.parse(t)
            for n, x in zip(steps, g["at"]):
                r = Run(m)
                h = r.run(n)
                self.assertEqual(x, [h, r.steps, r.ones(), r.config_str()], (t, n))
            py = []
            for k, (s, side, r) in enumerate(records(m, 3000)):
                if k >= 60:
                    break
                py.append([s, side, r.tape.hi - r.tape.lo, r.config_str()])
            self.assertEqual(g["recs"], py, t)


class TestSync(unittest.TestCase):
    BB2 = "1RB1LB_1LA---_------_------_------_------"
    DETOUR = "1LD1LB_1LA---_------_0RE1RE_1RB1RB_------"    # BB(2) with a three-step detour on A0

    def test_toy_closes_and_lean_current(self):
        """The toy pair closes with windows of 2 cells, and the committed Lean file is what the tool writes now."""
        (AL, AR, S), pairs, certs = syncpair.closure(self.BB2, self.DETOUR, False, 2)
        C = json.loads(json.dumps(syncpair.dump(self.BB2, self.DETOUR, False, AL, AR, S, pairs, certs)))
        with open(os.path.join(TOOLS, "lean", "Test", "Sync.lean")) as f:
            self.assertEqual(f.read().rstrip("\n"), syncpair.lean_file(C, "SyncToy").rstrip("\n"))

    def test_resync_toy(self):
        r = syncpair.resync(self.BB2, self.DETOUR, False, 100)
        self.assertEqual(r[0], "bothhalt")

    def test_nonequivalent_fails(self):
        """A pair whose halting differs cannot close."""
        with self.assertRaises(syncpair.Fail):
            syncpair.closure(self.BB2, "1RB1LB_1LA1LA_------_------_------_------", False, 2)

    def test_cfghash_mirror(self):
        """The mirror hashes of a run are the forward hashes of the mirror-image machine's run, step for step."""
        exe = cc("cfghash")
        rng = random.Random(3)
        for _ in range(20):
            text = random_machine(rng, 4)
            mir = syncpair.mirror_text(text)
            a = subprocess.run([exe, text, "300", "1"], capture_output=True, text=True, check=True).stdout.split("\n")
            b = subprocess.run([exe, mir, "300", "1"], capture_output=True, text=True, check=True).stdout.split("\n")
            fa = [x[2:] for x in a if x.startswith("M ")]
            fb = [x[2:] for x in b if x.startswith("F ")]
            self.assertEqual(fa, fb, text)
            self.assertTrue(fa)


if __name__ == "__main__":
    try:
        unittest.main(verbosity=2)
    finally:
        shutil.rmtree(BUILD, ignore_errors=True)
