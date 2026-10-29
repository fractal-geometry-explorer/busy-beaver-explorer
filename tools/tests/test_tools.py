"""Tests of the shared tools: the Python reference simulator, the C simulator against it, the symbolic prover
(against concrete runs, and through Lean when a Lean binary is installed), the parts protocol and merge, the
invariant finder, the Lean generator and the status-page builder.

usage: python3 tools/tests/test_tools.py        (from anywhere; builds the C programs into a temporary directory)
"""
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
from bbtools import symtm, leangen, invariants  # noqa: E402
from bbtools.explore import blocks  # noqa: E402
import merge_parts  # noqa: E402
import build_status  # noqa: E402

THIS = "1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB"
HOLDOUT = "1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE"
CHAMPIONS = {   # machine: steps to halt from blank tape, bbchallenge count
    "1RB1LB_1LA1RZ": 6,
    "1RB1RZ_1LB0RC_1LC1LA": 21,
    "1RB1LB_1LA0LC_1RZ1LD_1RD0RA": 107,
}
BB5 = "1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA"

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
        for name, text in [("BB2", "1RB1LB_1LA1RZ"), ("BB4", "1RB1LB_1LA0LC_1RZ1LD_1RD0RA")]:
            with open(os.path.join(TOOLS, "lean", "Test", name + ".lean")) as f:
                self.assertEqual(f.read(), leangen.machine_lean(text, "Test." + name))


class TestStatusPage(unittest.TestCase):
    def test_build(self):
        spec = {"title": "T", "machine": THIS, "claims": [
            {"level": "kernel", "title": "k", "text": "a"}, {"level": "open", "title": "o", "text": "b"}]}
        page = build_status.build(spec)
        self.assertIn("t-kernel", page)
        self.assertIn('class="card open"', page)
        with self.assertRaises(ValueError):
            build_status.build({"title": "T", "machine": THIS, "claims": [{"level": "proved", "title": "x", "text": ""}]})


if __name__ == "__main__":
    try:
        unittest.main(verbosity=2)
    finally:
        shutil.rmtree(BUILD, ignore_errors=True)
