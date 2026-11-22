"""The left-end ticks (rebuilds) of 1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---: a rule on the front of the block list,
the ordinary chain law on the rest.

usage: ./blocks 1e10 | python3 holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/py/front.py classify
           every left-end tick: its front shape, the shape's rule in block notation, and a check of the rule against
           the next list of the run; writes lean/front_shapes.txt (the shapes that occur)
       python3 holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/py/front.py lean
           writes lean/Front.lean from lean/front_shapes.txt

A left-end tick is a tick whose rule (py/ticks.py) needs the left end of the tape, or in which the head reaches the
first 1 of the tape (the third column of c/blocks.c is at most 0).  Write its list as

    F . m1 . m2 . ... . mk          k even, every m_i even, F the front (it ends with the block a)

with k as large as possible.  The left pass over the m's is the ordinary one (`left_pass` of lean/Chain.lean), and
so is the right pass back (`right_pass`), so the tick is one new piece, the *front piece*: from the configuration
the left pass leaves at a, `⟨Rot b F, D010 R, D⟩` (b the block m1), the machine reaches `⟨F', A0100 b R, A⟩` with R
untouched.  This script finds the shape of F for each tick (each block of F a variable of fixed parity, or a
literal 1), runs the front piece symbolically (`bbtools.symtm`), and composes it in Lean with `enter`,
`left_pass`, `right_pass`, `leave` into a theorem for the whole tick, for every list of pairs (any k) and every
value of the variables.

Ticks whose front piece does not close are the *copy ticks* (walls): their front ends `| 1` and the head loops
between the left end and m1, copying m1 into a new first block of about twice its length; the loop reads m1 cell
by cell, so the piece needs an induction (open here; described in the README).
"""
import os
import re
import sys
from collections import OrderedDict

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools.symtm import (Config, run, TouchContext, NeedSplit, Rep, Lin, Blank, Ctx, canon, tokens,  # noqa: E402
                           left_term, rules_file)
from bbtools.machine import Machine  # noqa: E402
import ticks  # noqa: E402
from tapeeq import rule  # noqa: E402

M = Machine.parse("1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---")
NS = "H103746"
SHAPES = os.path.join(HERE, "..", "lean", "front_shapes.txt")
TARGET = canon(tokens("(0101)^b 0 1 0 0 R"))


def parse_list(s):
    return list(map(int, re.findall(r"\d+", s))), re.findall(r"[|.]", s)


def fmt_list(nums, seps):
    out = str(nums[0])
    for s, n in zip(seps, nums[1:]):
        out += s + str(n)
    return out


# ---------------------------------------------------------------- shapes
def shape_of(nums, seps):
    """Block j: '1' if it has length 1, else 'e' or 'o' by parity.  A shape is 'e|o.1|e' etc."""
    out = ""
    for j, n in enumerate(nums):
        out += "1" if n == 1 else ("e" if n % 2 == 0 else "o")
        if j < len(seps):
            out += seps[j]
    return out


def shape_parse(shape):
    return re.findall(r"[eo1]", shape), re.findall(r"[|.]", shape)


def block_str(kind, v):
    if kind == "1":
        return "1 0"
    if kind == "e":                      # 2v+2 pairs
        return f"(1010)^{v}+1"
    return f"1 0 (1010)^{v}+1"          # 2v+3 pairs


def front_tape(shape):
    kinds, seps = shape_parse(shape)
    parts = ["0^inf"]
    for j, k in enumerate(kinds):
        parts.append(block_str(k, f"v{j}"))
        if j < len(seps):
            parts.append("1" if seps[j] == "|" else "0")
    return " ".join(parts)


def split_index(nums, seps):
    """the smallest a such that after block a come k >= 2 (even) even blocks with separators 0"""
    for a in range(len(nums) - 1):
        rest, rs = nums[a + 1:], seps[a:]
        if len(rest) >= 2 and len(rest) % 2 == 0 and all(s == "." for s in rs) and all(x % 2 == 0 for x in rest):
            return a
    return None


def at_target(c):
    return c.state == 0 and canon(list(c.right)) == TARGET


def front_piece(shape, max_moves=50000):
    """the symbolic run of the front piece; None if it does not close (touches R, needs a split, too long)"""
    c = Config.parse(front_tape(shape) + " 0 1 0 1 (0101)^b D> 0 1 0 R")
    try:
        run(M, c, at_target, max_moves=max_moves, rotate=True)
    except (TouchContext, NeedSplit, RuntimeError):
        return None
    return c


# ---------------------------------------------------------------- block rule of a shape
def to_blocks(left):
    """Block notation of the left tape at a right-end turn (`... A> 1 1 0^inf`), lengths as Lin."""
    segs = []
    for t in left:
        if isinstance(t, Blank):
            continue
        if isinstance(t, Rep):
            segs.append((t.word[0], t.word[-1], len(t.word) * t.n))
        else:
            segs.append((t, t, Lin(1)))
    while segs and segs[0][0] == 0 and segs[0][2] == Lin(1):
        segs.pop(0)
    out, cur, prev = [], Lin(0), None
    for f, last, n in segs:
        if prev is not None and prev == f:
            if f == 1:
                out += [cur - 1, "|"]
                cur = Lin(0)
            else:
                out += [cur, "."]
                cur = Lin(-1)
        cur, prev = cur + n, last
    out.append(cur)
    return [x if isinstance(x, str) else Lin(x.k // 2, {k: v // 2 for k, v in x.c.items()}) for x in out]


def at_end(c):
    r = c.right
    return (c.state == 0 and len(r) == 3 and r[0] == 1 and r[1] == 1 and isinstance(r[2], Blank)
            and not c.steps.is_zero())


SUFFIX = 4      # the rule is printed with four blocks m1..m4 after the front


def block_rule(shape, k=SUFFIX):
    """(before, after, after_list, steps): the tick of `shape . m1 . ... . mk` in block notation, the front's
    lengths named n0, n1, ... and the chain m1..mk, computed by one symbolic run of the whole tick."""
    kinds, seps = shape_parse(shape)
    s = front_tape(shape) + "".join(f" 0 (1010)^w{i}+1" for i in range(1, k + 1)) + " A> 1 1 0^inf"
    c = Config.parse(s)
    run(M, c, at_end, max_moves=400000, rotate=True)
    names = {f"v{j}": (f"n{j}", kinds[j]) for j in range(len(kinds))}
    names.update({f"w{i}": (f"m{i}", "e") for i in range(1, k + 1)})
    after = []
    for x in to_blocks(c.left):
        if isinstance(x, str):
            after.append(x)
            continue
        # x = sum cf*v + const; the block of v has n = 2v+2 (even) or 2v+3 (odd) pairs
        o = Lin(x.k)
        for v, cf in x.c.items():
            nm, kd = names[v]
            assert cf % 2 == 0, (shape, x)
            o = o + Lin(-(cf // 2) * (2 if kd == "e" else 3), {nm: cf // 2})
        after.append(o)
    before = []
    for j, kd in enumerate(kinds):
        before.append("1" if kd == "1" else f"n{j}")
        if j < len(seps):
            before.append(seps[j])
    for i in range(1, k + 1):
        before += [".", f"m{i}"]
    return "".join(before), "".join(x if isinstance(x, str) else repr(x) for x in after), after, c.steps


def predict(after, nums, nf):
    """the list after the tick: the rule `after` (for this k) with the run's lengths substituted"""
    env = {f"n{j}": nums[j] for j in range(nf)}
    env.update({f"m{i}": nums[nf + i - 1] for i in range(1, len(nums) - nf + 1)})
    out = ""
    for x in after:
        if isinstance(x, str):
            out += x
        else:
            v = x.subs(env)
            out += str(v.k if isinstance(v, Lin) else v)
    return out


# ---------------------------------------------------------------- classify
def classify():
    lines = [ln.split() for ln in sys.stdin if ln.strip() and not ln.startswith("HALT")]
    shapes, walls, other = OrderedDict(), [], []
    nleft = 0
    cache = {}
    for i in range(len(lines) - 1):
        step, lst = lines[i][0], lines[i][1]
        nums, seps = parse_list(lst)
        low = int(lines[i + 1][2]) if len(lines[i + 1]) > 2 else 1
        r = ticks.tick(nums, seps) if len(nums) >= 2 else None
        if r is not None and low > 0:
            continue
        nleft += 1
        nxt = lines[i + 1][1]
        a = split_index(nums, seps)
        if a is None:
            other.append((step, lst, nxt))
            continue
        shape = shape_of(nums[:a + 1], seps[:a])
        if shape not in cache:
            c = front_piece(shape)
            cache[shape] = (c, block_rule(shape) if c is not None else None)
        c, br = cache[shape]
        if c is None:
            walls.append((step, lst, nxt))
            continue
        k = len(nums) - a - 1
        if (shape, k) not in cache:
            cache[(shape, k)] = block_rule(shape, k)
        pred = predict(cache[(shape, k)][2], nums, a + 1)
        ok = pred == nxt
        e = shapes.setdefault(shape, [0, 0, step, lst, nxt, br])
        e[0] += 1
        e[1] += ok
        if not ok:
            print(f"MISMATCH {step} {lst}: rule gives {pred}, run gives {nxt}")
    print(f"{nleft} left-end ticks: {sum(e[0] for e in shapes.values())} through {len(shapes)} front shapes, "
          f"{len(walls)} copy ticks, {len(other)} other\n")
    print("count  checked  shape            rule (block notation, m1..m4 the chain after the front)")
    for shape, (n, ok, step, lst, nxt, br) in sorted(shapes.items(), key=lambda kv: -kv[1][0]):
        print(f"{n:5d} {ok:8d}   {shape:16s} {br[0]}  ->  {br[1]}   first: {step} {lst} -> {nxt}")
    print("\ncopy ticks:")
    for step, lst, nxt in walls:
        print(f"  {step} {lst} -> {nxt}")
    print("\nother left-end ticks (no chain of k >= 2 even blocks after the front):")
    for step, lst, nxt in other:
        print(f"  {step} {lst} -> {nxt}")
    with open(SHAPES, "w") as f:
        f.write("# front shapes of the left-end ticks (py/front.py classify); one per line, with its count\n")
        for shape, e in shapes.items():
            f.write(f"{shape} {e[0]}\n")


# ---------------------------------------------------------------- Lean
DOC = """# The left-end ticks: a front piece and the ordinary passes

A left-end tick of the list `F . m1 . … . mk` (k even, the m's even) is the ordinary left pass over the m's
(`left_pass` of `Chain.lean`), one *front piece* at the left end of the tape, and the ordinary right pass back.
Each front piece below is a symbolic run (`py/front.py` with `tools/py/bbtools/symtm.py`) from the configuration
the left pass leaves, `⟨Rot b (F …), D010 R, .D⟩`, to `⟨F' …, A0100 b R, .A⟩`, for every value of its variables
(each block of the front has a variable, with its parity fixed: `(1010)^(v+1)` is an even block of 2v+2 pairs,
`10 (1010)^(v+1)` an odd one of 2v+3) and every tape R.  `tick_<shape>` is the whole tick, from one right-end turn
to the next, for every list of pairs `ps` and all `d`, `e`, as `tick_chain` is for the ticks that turn at a
separator.  The shapes are those of the left-end ticks of the first 10^10 steps (`lean/front_shapes.txt`); the
README gives each rule in block notation."""


def lean_name(shape):
    return shape.replace("|", "I").replace(".", "_")


def gen_lean():
    shapes = [ln.split()[0] for ln in open(SHAPES) if ln.strip() and not ln.startswith("#")]
    parts = ["set_option maxRecDepth 100000\nset_option maxHeartbeats 4000000\n"]
    for shape in shapes:
        nm = lean_name(shape)
        kinds, _ = shape_parse(shape)
        vs = [f"v{j}" for j, k in enumerate(kinds) if k != "1"]
        ft = front_tape(shape)
        c = front_piece(shape)
        assert c is not None, shape
        fin_left = " ".join(map(str, c.left))
        binders = " ".join(vs)
        bnd = f" ({binders} : Nat)" if vs else ""
        args = (" " + binders) if vs else ""
        br = block_rule(shape)
        parts.append(f"/-- The front `{shape}` (`{br[0]} -> {br[1]}`), before the front piece. -/\n"
                     f"def F_{nm}{bnd} : Tape := {left_term(tokens(ft))}\n"
                     f"/-- The front `{shape}` after the front piece. -/\n"
                     f"def F'_{nm}{bnd} : Tape := {left_term(c.left)}\n")
        parts += rule(f"front_{nm}", ft + " 0 1 0 1 (0101)^b D> 0 1 0 R", fin_left + " A> (0101)^b 0 1 0 0 R",
                      vs + ["b"], f"⟨Rot b (F_{nm}{args}), D010 R, .D⟩", f"⟨F'_{nm}{args}, A0100 b R, .A⟩",
                      f"The front piece of `{shape}`.")
        parts.append(f"""/-- The left-end tick of `{shape} . m1 . … . mk` (k even, any k), in block notation
`{br[0]}  ->  {br[1]}` (shown for k = 4), from one right-end turn to the next. -/
theorem tick_{nm}{bnd} (d e : Nat) (ps : List (Nat × Nat)) : ∃ n,
    steps n ⟨Q d e (P ps (F_{nm}{args})), cons true (cons true blank), .A⟩ =
      some ⟨Fin d e (W ps d (F'_{nm}{args})), cons true (cons true blank), .A⟩ := by
  obtain ⟨n1, h1⟩ := left_pass (F_{nm}{args}) ps d (R0 e)
  obtain ⟨n2, h2⟩ := right_pass (F'_{nm}{args}) ps d (R0 e)
  exact ⟨_, steps_seq trans (enter d e (P ps (F_{nm}{args})))
    (steps_seq trans h1 (steps_seq trans (front_{nm}{args} _ _) (steps_seq trans h2 (leave d e (W ps d (F'_{nm}{args}))))))⟩
""")
    txt = rules_file("Chain", NS, parts, DOC)
    with open(os.path.join(HERE, "..", "lean", "Front.lean"), "w") as f:
        f.write(txt)
    print(f"wrote lean/Front.lean: {len(shapes)} shapes")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "lean":
        gen_lean()
    else:
        classify()
