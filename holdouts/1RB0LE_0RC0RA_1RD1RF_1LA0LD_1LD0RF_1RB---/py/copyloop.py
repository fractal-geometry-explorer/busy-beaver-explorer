"""The copy ticks of 1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB--- in Lean: the copy loop for any front, and the whole
tick for every front shape of the run.

usage: python3 holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/py/copyloop.py [classify.txt]
           writes lean/Copy.lean for the P shapes in lean/copy_shapes.txt; with classify.txt (the output of
           `py/front.py classify`) it first rewrites lean/copy_shapes.txt from the copy ticks listed there;
           writes lean/copy_results.txt (per shape: the shift of x, the offsets of the block variables, the ends)
       python3 holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/py/copyloop.py check classify.txt
           for every copy tick of the run: the theorem it is an instance of, and its end read as a block list against
           the list the run reaches

A copy tick reads `P | 1 . X . m1 . ... . mk` (k odd, X and the m's even).  The left pass of lean/Chain.lean ends
on X; from there the head goes back and forth between the left end of the tape and X, and every half round moves one
pair `10` of X into a new first block.  After the first rounds (the *entry*, which reworks P) the tape right of the
head, at the left end in state D, is

    KR = 1 (10)^(2j+2)  0 (10)^(2b1+2)  0 (10)^(2b2+2)  ...  0 (10)^(2bm+2)  0 0 (10)^(2r) Z

(`Kj j (CS bs (X0 r Z))` in Lean): j the pairs copied, the reworked P as the even blocks bs, r the pairs of X left.
A round is seven local pieces: `el1` (left end, to the first block), `crossB` over each block (`passB`, an
induction on bs), `xa` at X, `crossD` back over each block (`passD`), `el2`, `passB`, `xb`, `passD`, `el3`.  So
`round` holds for every list bs, and `loop` (induction on r) takes KR to r = 0.

For each P shape (blocks `e` even, `o` odd, `1`, with their separators, as in py/front.py) the entry and the two
exits (`exit3` when the chain goes on, k >= 3; `exit1` when k = 1) are symbolic runs with a variable for every
block of P, for j and for the chain; the entry's end (j0, bs, r0 as linear forms) is found by running it on a few
values and is then proved symbolically.  `copy_<S>_long` and `copy_<S>_one` compose the pieces with `enter`,
`left_pass`, `lu`, `right_pass`, `leave` into the whole tick, for every X, every value of P's blocks, every chain
and every list of pairs.  The shape `o|1|o` copies the block Y between the two 1s instead of X (`gen_y`, the same
loop with Y's pairs in place of X's); in `o|1|o|o.e|e|o|o.e|e|o` the front `3|1|7` comes up during the entry and
copies its 7, so that entry is a symbolic run for the one value 7 of that block (`FIX`).
"""
import os
import re
import sys
from collections import OrderedDict

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools.symtm import (Config, run, canon, tokens, left_term, right_term, rules_file, parse_lin, Rep, Ctx, Blank, Lin,  # noqa: E402
                           TouchContext, NeedSplit)
from bbtools.machine import Machine  # noqa: E402
from tapeeq import rule  # noqa: E402
from front import shape_parse, block_str, lean_name  # noqa: E402

M = Machine.parse("1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---")
NS = "H103746"
SHAPES = os.path.join(HERE, "..", "lean", "copy_shapes.txt")
RESULTS = os.path.join(HERE, "..", "lean", "copy_results.txt")
SKIP = {"o|1|o"}


# ---------------------------------------------------------------- the loop, for any list of blocks
PIECES = [
    ("crossB", "L B> 0 1 0 1 0 (1010)^b R", "L 0 1 1 (0101)^b 0 1 B> R", ["b"],
     "⟨L, Ck b R, .B⟩", "⟨Bk b L, R, .B⟩", "The head crosses a block of the loop to the right."),
    ("crossD", "L 0 1 1 (0101)^b 0 1 0 D> 1 R", "L 0 D> 1 0 1 0 1 0 (1010)^b R", ["b"],
     "⟨cons false (Bk b L), cons true R, .D⟩", "⟨cons false L, cons true (Ck b R), .D⟩",
     "The head crosses a block of the loop back to the left, restoring it."),
    ("xa", "L B> 0 0 (1010)^r+1 Z", "L 0 D> 1 0 0 1 0 (1010)^r Z", ["r"],
     "⟨L, X0 (r + 1) Z, .B⟩", "⟨cons false L, cons true (X1 r Z), .D⟩", "The first half round takes a pair of X."),
    ("xb", "L B> 0 0 1 0 (1010)^r Z", "L 0 D> 1 0 0 (1010)^r Z", ["r"],
     "⟨L, X1 r Z, .B⟩", "⟨cons false L, cons true (X0 r Z), .D⟩", "The second half round takes a pair of X."),
    ("el1", "0^inf D> 1 1 0 (1010)^j 1 0 R", "0^inf 1 0 (1010)^j 1 0 1 0 1 B> R", ["j"],
     "⟨blank, Kj j R, .D⟩", "⟨J1 j, R, .B⟩", "At the left end, at the start of a round."),
    ("el2", "0^inf 1 0 (1010)^j 1 0 1 0 1 0 D> 1 R", "0^inf 1 0 1 0 1 (0101)^j 0 1 0 1 0 1 B> R", ["j"],
     "⟨cons false (J1 j), cons true R, .D⟩", "⟨J2 j, R, .B⟩", "At the left end, between the half rounds."),
    ("el3", "0^inf 1 0 1 0 1 (0101)^j 0 1 0 1 0 1 0 D> 1 R", "0^inf D> 1 1 0 (1010)^j+2 1 0 R", ["j"],
     "⟨cons false (J2 j), cons true R, .D⟩", "⟨blank, Kj (j + 2) R, .D⟩", "At the left end, at the end of a round."),
]

DEFS = [  # name, binders, kind (left or right tape), tape string, doc
    ("Kj", "(j : Nat) (R : Tape)", "r", "1 1 0 (1010)^j 1 0 R",
     "`1 (10)^(2j+2) R`: the new first block, right of the head at the left end."),
    ("Ck", "(b : Nat) (R : Tape)", "r", "0 1 0 1 0 (1010)^b R", "`0 (10)^(2b+2) R`: a block of the reworked front."),
    ("Bk", "(b : Nat) (L : Tape)", "l", "L 0 1 1 (0101)^b 0 1", "The same block after the head crossed it to the right."),
    ("X0", "(r : Nat) (Z : Tape)", "r", "0 0 (1010)^r Z", "`0 0 (10)^(2r) Z`: what is left of X."),
    ("X1", "(r : Nat) (Z : Tape)", "r", "0 0 1 0 (1010)^r Z", "The same in the middle of a round."),
    ("J1", "(j : Nat)", "l", "0^inf 1 0 (1010)^j 1 0 1 0 1", "The left end in the first half round."),
    ("J2", "(j : Nat)", "l", "0^inf 1 0 1 0 1 (0101)^j 0 1 0 1 0 1", "The left end in the second half round."),
]


def loop_defs():
    out = []
    for nm, b, kind, s, doc in DEFS:
        term = right_term(tokens(s)) if kind == "r" else left_term(tokens(s))
        out.append(f"/-- {doc} -/\ndef {nm} {b} : Tape := {term}\n")
        if nm == "Bk":
            out.append("""/-- The blocks of the reworked front, the first one nearest the left end. -/
def CS : List Nat → Tape → Tape
  | [], R => R
  | b :: bs, R => Ck b (CS bs R)
/-- The same blocks, crossed to the right. -/
def BS : List Nat → Tape → Tape
  | [], L => L
  | b :: bs, L => BS bs (Bk b L)
""")
    return "".join(out)


LOOP_THMS = """theorem passB : ∀ (bs : List Nat) (L R : Tape), ∃ n,
    steps n ⟨L, CS bs R, .B⟩ = some ⟨BS bs L, R, .B⟩ := by
  intro bs
  induction bs with
  | nil => intro L R; exact ⟨0, rfl⟩
  | cons b bs ih =>
    intro L R
    obtain ⟨n, hn⟩ := ih (Bk b L) R
    exact ⟨_, steps_seq trans (crossB b L (CS bs R)) hn⟩

theorem passD : ∀ (bs : List Nat) (L R : Tape), ∃ n,
    steps n ⟨cons false (BS bs L), cons true R, .D⟩ = some ⟨cons false L, cons true (CS bs R), .D⟩ := by
  intro bs
  induction bs with
  | nil => intro L R; exact ⟨0, rfl⟩
  | cons b bs ih =>
    intro L R
    obtain ⟨n, hn⟩ := ih (Bk b L) R
    exact ⟨_, steps_seq trans hn (crossD b L (CS bs R))⟩

/-- One round of the copy loop, for any reworked front `bs`: two pairs of X move into the new first block. -/
theorem round (bs : List Nat) (j r : Nat) (Z : Tape) : ∃ n,
    steps n ⟨blank, Kj j (CS bs (X0 (r + 1) Z)), .D⟩ = some ⟨blank, Kj (j + 2) (CS bs (X0 r Z)), .D⟩ := by
  obtain ⟨n1, h1⟩ := passB bs (J1 j) (X0 (r + 1) Z)
  obtain ⟨n2, h2⟩ := passD bs (J1 j) (X1 r Z)
  obtain ⟨n3, h3⟩ := passB bs (J2 j) (X1 r Z)
  obtain ⟨n4, h4⟩ := passD bs (J2 j) (X0 r Z)
  exact ⟨_, steps_seq trans (el1 j _) (steps_seq trans h1 (steps_seq trans (xa r _ Z) (steps_seq trans h2
    (steps_seq trans (el2 j _) (steps_seq trans h3 (steps_seq trans (xb r _ Z) (steps_seq trans h4
      (el3 j _))))))))⟩

/-- The copy loop: all r remaining pairs of X move into the new first block. -/
theorem loop (bs : List Nat) : ∀ (r j : Nat) (Z : Tape), ∃ n,
    steps n ⟨blank, Kj j (CS bs (X0 r Z)), .D⟩ = some ⟨blank, Kj (j + 2 * r) (CS bs (X0 0 Z)), .D⟩ := by
  intro r
  induction r with
  | zero => intro j Z; exact ⟨0, rfl⟩
  | succ r ih =>
    intro j Z
    obtain ⟨n1, h1⟩ := round bs j r Z
    obtain ⟨n2, h2⟩ := ih (j + 2) Z
    rw [show j + 2 + 2 * r = j + 2 * (r + 1) by omega] at h2
    exact ⟨_, steps_seq trans h1 h2⟩
"""


# ---------------------------------------------------------------- tape strings
def lin_s(x):
    return str(Lin(x)) if not isinstance(x, Lin) else str(x)


def rep_s(word, n):
    n = n if isinstance(n, Lin) else (parse_lin(n) if isinstance(n, str) else Lin(n))
    return "" if n.is_zero() else f"({word})^{n}"


def kr_s(j, bs, r, Z):
    """Kj j (CS bs (X0 r Z)) as a tape string"""
    parts = ["1 1 0", rep_s("1010", j), "1 0"]
    for b in bs:
        parts += ["0 1 0 1 0", rep_s("1010", b)]
    parts += ["0 0", rep_s("1010", r), Z]
    return " ".join(" ".join(parts).split())


OFF = {}     # shape -> {variable: offset}: the block variable v stands for v + offset (found by gen_shape)


# shape -> {variable: value}: a block of the front fixed to one value.  In `o|1|o|o.e|e|o|o.e|e|o` the front
# `3|1|Y` comes up during the entry and copies Y (as in gen_y), a loop of its own inside the entry, so the entry is
# one symbolic run only for one value of Y.
FIX = {"o|1|o|o.e|e|o|o.e|e|o": {"v2": 2}}


def fc_s(shape):
    kinds, seps = shape_parse(shape)
    off = OFF.get(shape, {})
    fix = FIX.get(shape, {})
    parts = ["0^inf"]
    for j, k in enumerate(kinds):
        v = f"v{j}"
        parts.append(block_str(k, str(fix[v]) if v in fix else f"{v}+{off[v]}" if off.get(v) else v))
        if j < len(seps):
            parts.append("1" if seps[j] == "|" else "0")
    return " ".join(parts + ["1 1 0"])


def shape_vars(shape):
    kinds, _ = shape_parse(shape)
    return [f"v{j}" for j, k in enumerate(kinds) if k != "1" and f"v{j}" not in FIX.get(shape, {})]


def subst(s, env):
    """replace the exponents of s by their values"""
    return re.sub(r"\(([01]+)\)\^(\S+)", lambda m: f"({m.group(1)})^{parse_lin(m.group(2)).subs(env)}", s)


# ---------------------------------------------------------------- the entry, found on values
CTX_Z = "Z"


def bits_before_ctx(toks):
    out = []
    for t in toks:
        if isinstance(t, Ctx):
            return "".join(map(str, out)), t.name
        if isinstance(t, Rep):
            out += list(t.word) * t.n.subs({})
        elif isinstance(t, Blank):
            return None, None
        else:
            out.append(t)
    return None, None


KRE = re.compile(r"^1((?:10)+)((?:0(?:10)+)*)00((?:10)*)0$")


def kr_parse(c):
    """(j, bs, r) if c is ⟨blank, Kj j (CS bs (X0 r (0 Z))), D⟩"""
    if c.state != 3 or any(not isinstance(t, Blank) for t in c.left) or c.steps.is_zero():
        return None
    b, ctx = bits_before_ctx(canon(list(c.right)))
    if b is None or ctx != CTX_Z:
        return None
    m = KRE.match(b)
    if not m:
        return None
    j2 = len(m.group(1)) // 2
    blocks = [len(x) // 2 for x in re.findall(r"0((?:10)+)", m.group(2))]
    r2 = len(m.group(3)) // 2
    if j2 % 2 or r2 % 2 or any(x % 2 for x in blocks):
        return None
    return (j2 - 2) // 2, [(x - 2) // 2 for x in blocks], r2 // 2


def entry_start(shape):
    return fc_s(shape) + " 0 1 0 1 (0101)^x D> 0 1 0 Z"


def entry_values(shape, env):
    c = Config.parse(subst(entry_start(shape), env))
    found = []

    def stop(c):
        p = kr_parse(c)
        if p:
            found.append(p)
        return bool(p)
    run(M, c, stop, max_moves=10 ** 6, rotate=True)
    return found[0]


def fit(shape):
    """j0, bs, r0 of the entry's end as linear forms in the shape's variables and x"""
    vs = shape_vars(shape) + ["x"]
    base = {v: 7 + 3 * i for i, v in enumerate(vs)}
    base["x"] = 60
    b0 = entry_values(shape, base)
    diffs = {}
    for v in vs:
        env = dict(base)
        env[v] += 1
        diffs[v] = entry_values(shape, env)
    if any(len(d[1]) != len(b0[1]) for d in diffs.values()):
        raise ValueError(f"{shape}: the number of blocks depends on the values")

    def lf(get):
        coef = {v: get(diffs[v]) - get(b0) for v in vs}
        k = get(b0) - sum(coef[v] * base[v] for v in vs)
        return Lin(k, coef)
    j0 = lf(lambda t: t[0])
    bs = [lf(lambda t, i=i: t[1][i]) for i in range(len(b0[1]))]
    r0 = lf(lambda t: t[2])
    # check on other values
    env = {v: 11 + 5 * i for i, v in enumerate(vs)}
    env["x"] = 75
    t = entry_values(shape, env)
    assert t == (j0.subs(env), [b.subs(env) for b in bs], r0.subs(env)), (shape, t)
    return j0, bs, r0


# ---------------------------------------------------------------- Lean, per shape
TARGET = canon(tokens("(0101)^d 0 1 0 0 R"))


def at_target(c):
    return c.state == 0 and canon(list(c.right)) == TARGET


def at_end(c):
    r = c.right
    return c.state == 0 and len(r) == 3 and r[0] == 1 and r[1] == 1 and not c.steps.is_zero()


def end_config(start, stop):
    c = Config.parse(start)
    run(M, c, stop, max_moves=300000, rotate=True)
    return c


def gen_shape(shape):
    """gen_shape1, with the block variables shifted up (v -> v + 1) while a run needs a split on one of them"""
    for _ in range(12):
        try:
            return gen_shape1(shape)
        except Exception as e:
            m = (re.search(r"NeedSplit: \(\w+\)\^(\S+)", str(e)) or re.search(r"negative term in (\S+)", str(e))
                 or (re.search(r"\(\w+\)\^(\S+)", str(e)) if isinstance(e, NeedSplit) else None))
            v = m and parse_lin(m.group(1))
            print(f"   {shape}: {type(e).__name__}: {str(e)[:120]}")
            if not v or not v.vars() <= set(shape_vars(shape)):
                raise
            for name in v.vars():
                OFF.setdefault(shape, {})[name] = OFF.get(shape, {}).get(name, 0) + 1
    raise RuntimeError(shape)


def gen_shape1(shape):
    nm = lean_name(shape)
    vs = shape_vars(shape)
    j0, bs, r0 = fit(shape)
    # write x so that r0 has no negative constant: x = x' + k
    k = max(0, -r0.k)
    shift = {"x": Lin(k, {"x": 1})}

    def sh(lv):
        out = Lin(lv.k)
        for v, a in lv.c.items():
            out = out + a * (shift.get(v, Lin(v)))
        return out
    j0, bs, r0 = sh(j0), [sh(b) for b in bs], sh(r0)
    xk = Lin(k, {"x": 1})
    bnd = f" ({' '.join(vs)} : Nat)" if vs else ""
    args = (" " + " ".join(vs)) if vs else ""
    blist = "[" + ", ".join(b.lean() for b in bs) + "]"
    bsl = [str(b) for b in bs]
    jj = Lin("j")
    W3, W1 = "0 1 0 (1010)^c+1 0 1 0 1 0 1 0 (1010)^d 0 R", "0 (1010)^e+1 1 0^inf"
    g3 = end_config("0^inf D> " + kr_s(jj, bsl, 0, W3), at_target)
    g1 = end_config("0^inf D> " + kr_s(jj, bsl, 0, W1), at_end)
    # A shape with a fixed block has blocks of one value in the loop.  A literal count in a run is costly in Lean
    # (it lets the kernel unfold the steps), so the exits are proved with a variable w_i for each such block and
    # used at its value.
    cix = [i for i, b in enumerate(bs) if not b.vars()] if shape in FIX else []
    wv = [f"w{i}" for i in cix]
    bsl_e = [f"w{i}" if i in cix else s for i, s in enumerate(bsl)]
    blist_e = "[" + ", ".join(f"w{i}" if i in cix else b.lean() for i, b in enumerate(bs)) + "]"
    wargs = "".join(f" ({bs[i].lean()})" for i in cix)
    bnd_e = f" ({' '.join(vs + wv)} : Nat)" if vs + wv else ""
    args_e = (" " + " ".join(vs + wv)) if vs + wv else ""
    g3e = end_config("0^inf D> " + kr_s(jj, bsl_e, 0, W3), at_target) if cix else g3
    g1e = end_config("0^inf D> " + kr_s(jj, bsl_e, 0, W1), at_end) if cix else g1
    parts = [f"/-- `{shape} | 1 .`: the tape left of X in a copy tick with front `{shape}`. -/\n"
             f"def FC_{nm}{bnd} : Tape := {left_term(tokens(fc_s(shape)))}\n"
             f"/-- What the copy loop leaves on the left, front `{shape}`, when the chain goes on. -/\n"
             f"def G3_{nm}{bnd_e} (j c : Nat) : Tape := {left_term(g3e.left)}\n"
             f"/-- The same when the chain has one block. -/\n"
             f"def G1_{nm}{bnd_e} (j e : Nat) : Tape := {left_term(g1e.left)}\n"]
    xs = xk.lean()
    parts += rule(f"entry_{nm}", subst_x(entry_start(shape), xk),
                  "0^inf D> " + kr_s(j0, bsl, r0, "0 Z"), vs + ["x"],
                  f"⟨Rot ({xs}) (FC_{nm}{args}), D010 Z, .D⟩",
                  f"⟨blank, Kj ({j0.lean()}) (CS {blist} (X0 ({r0.lean()}) (cons false Z))), .D⟩",
                  f"Front `{shape}`: from the end of the left pass at X into the copy loop.")
    parts += rule(f"exit3_{nm}", "0^inf D> " + kr_s(jj, bsl_e, 0, W3),
                  " ".join(map(str, g3e.left)) + " A> (0101)^d 0 1 0 0 R", vs + wv + ["j", "c", "d"],
                  f"⟨blank, Kj j (CS {blist_e} (X0 0 (cons false (U (c + 1) d R)))), .D⟩",
                  f"⟨G3_{nm}{args_e} j c, A0100 d R, .A⟩",
                  f"Front `{shape}`: the end of the loop when the chain goes on, back to the right pass.")
    parts += rule(f"exit1_{nm}", "0^inf D> " + kr_s(jj, bsl_e, 0, W1),
                  " ".join(map(str, g1e.left)) + " A> 1 1 0^inf", vs + wv + ["j", "e"],
                  f"⟨blank, Kj j (CS {blist_e} (X0 0 (cons false (R0 e)))), .D⟩",
                  f"⟨G1_{nm}{args_e} j e, cons true (cons true blank), .A⟩",
                  f"Front `{shape}`: the end of the loop when the chain has one block, the next right-end turn.")
    jf = f"{j0.lean()} + 2 * ({r0.lean()})"
    parts.append(f"""/-- A whole copy tick of `{shape} | 1 . X . m1 . … . mk`, k ≥ 3 (X = 2({xs})+2, m1 = 2c+4, then the pairs `ps`,
then the last two blocks d, e), from one right-end turn to the next. -/
theorem copy_{nm}_long{bnd} (x c d e : Nat) (ps : List (Nat × Nat)) : ∃ n,
    steps n ⟨Q d e (P ps (Pc (c + 1) ({xs}) (FC_{nm}{args}))), cons true (cons true blank), .A⟩ =
      some ⟨Fin d e (W ps d (G3_{nm}{args}{wargs} ({jf}) c)), cons true (cons true blank), .A⟩ := by
  obtain ⟨n1, h1⟩ := left_pass (Pc (c + 1) ({xs}) (FC_{nm}{args})) ps d (R0 e)
  obtain ⟨n2, h2⟩ := loop {blist} ({r0.lean()}) ({j0.lean()}) (cons false (U (c + 1) (LP ps d (R0 e)).1 (LP ps d (R0 e)).2))
  obtain ⟨n3, h3⟩ := right_pass (G3_{nm}{args}{wargs} ({jf}) c) ps d (R0 e)
  exact ⟨_, steps_seq trans (enter d e _) (steps_seq trans h1 (steps_seq trans (lu ({xs}) (c + 1) _ _ _)
    (steps_seq trans (entry_{nm}{args} x _) (steps_seq trans h2 (steps_seq trans (exit3_{nm}{args}{wargs} _ c _ _)
      (steps_seq trans h3 (leave d e _)))))))⟩

/-- A whole copy tick of `{shape} | 1 . X . m1` (k = 1; X = 2({xs})+2, m1 = 2e+2), from one right-end turn to the
next. -/
theorem copy_{nm}_one{bnd} (x e : Nat) : ∃ n,
    steps n ⟨Q ({xs}) e (FC_{nm}{args}), cons true (cons true blank), .A⟩ =
      some ⟨G1_{nm}{args}{wargs} ({jf}) e, cons true (cons true blank), .A⟩ := by
  obtain ⟨n2, h2⟩ := loop {blist} ({r0.lean()}) ({j0.lean()}) (cons false (R0 e))
  exact ⟨_, steps_seq trans (enter ({xs}) e _) (steps_seq trans (entry_{nm}{args} x _)
    (steps_seq trans h2 (exit1_{nm}{args}{wargs} _ e)))⟩
""")
    return parts, (j0, bs, r0, k, " ".join(map(str, g3.left)), " ".join(map(str, g1.left)))


# ---------------------------------------------------------------- the front o|1|o: the copy of the block between the 1s
Y_SHAPE = "o|1|o"
Y_W = "1 0 0 0 (1010)^x 1 0 0 Z"      # what stands right of Y's pairs in the loop: X, moved, and the chain Z


def gen_y():
    """`3|1|Y|1 . X . C` (shape o|1|o, Y = 2v2+3): two rounds turn the front into `v0+2`-block and the loop copies Y
    (its v2+1 double pairs and one pair go into the new first block); X, untouched, ends 7 pairs longer."""
    shape, nm = Y_SHAPE, lean_name(Y_SHAPE)
    vs = shape_vars(shape)
    bnd, args = f" ({' '.join(vs)} : Nat)", " " + " ".join(vs)
    blist, bsl = "[v0 + 2]", ["v0+2"]
    jj = Lin("j")
    z3 = "1 0 (1010)^c+1 0 1 0 1 0 1 0 (1010)^d 0 R"
    z1 = "(1010)^e+1 1 0^inf"
    w3, w1 = Y_W.replace("Z", z3), Y_W.replace("Z", z1)
    g3 = end_config("0^inf D> " + kr_s(jj, bsl, 0, w3), at_target)
    g1 = end_config("0^inf D> " + kr_s(jj, bsl, 0, w1), at_end)
    parts = [f"/-- `{shape} | 1 .`: the tape left of X in a copy tick with front `{shape}`. -/\n"
             f"def FC_{nm}{bnd} : Tape := {left_term(tokens(fc_s(shape)))}\n"
             f"/-- Right of Y's pairs in its copy loop: X, and the chain Z. -/\n"
             f"def WY (x : Nat) (Z : Tape) : Tape := {right_term(tokens(Y_W))}\n"
             f"/-- What the copy of Y leaves on the left when the chain goes on. -/\n"
             f"def G3_{nm}{bnd} (x j c : Nat) : Tape := {left_term(g3.left)}\n"
             f"/-- The same when the chain has one block. -/\n"
             f"def G1_{nm}{bnd} (x j e : Nat) : Tape := {left_term(g1.left)}\n"]
    parts += rule(f"entry_{nm}", entry_start(shape), "0^inf D> " + kr_s(Lin(0), bsl, "v2+1", Y_W), vs + ["x"],
                  f"⟨Rot x (FC_{nm}{args}), D010 Z, .D⟩", f"⟨blank, Kj 0 (CS {blist} (X0 (v2 + 1) (WY x Z))), .D⟩",
                  f"Front `{shape}`: from the end of the left pass at X into the loop that copies Y.")
    parts += rule(f"exit3_{nm}", "0^inf D> " + kr_s(jj, bsl, 0, w3),
                  " ".join(map(str, g3.left)) + " A> (0101)^d 0 1 0 0 R", vs + ["x", "j", "c", "d"],
                  f"⟨blank, Kj j (CS {blist} (X0 0 (WY x (U (c + 1) d R)))), .D⟩",
                  f"⟨G3_{nm}{args} x j c, A0100 d R, .A⟩",
                  f"Front `{shape}`: the end of the loop when the chain goes on, back to the right pass.")
    parts += rule(f"exit1_{nm}", "0^inf D> " + kr_s(jj, bsl, 0, w1),
                  " ".join(map(str, g1.left)) + " A> 1 1 0^inf", vs + ["x", "j", "e"],
                  f"⟨blank, Kj j (CS {blist} (X0 0 (WY x (R0 e)))), .D⟩",
                  f"⟨G1_{nm}{args} x j e, cons true (cons true blank), .A⟩",
                  f"Front `{shape}`: the end of the loop when the chain has one block, the next right-end turn.")
    jf = "2 * (v2 + 1)"
    parts.append(f"""/-- A whole copy tick of `{shape} | 1 . X . m1 . … . mk`, k ≥ 3 (Y = 2 v2 + 3, X = 2x+2, m1 = 2c+4, then the
pairs `ps`, then the last two blocks d, e), from one right-end turn to the next: Y is copied, X moves on. -/
theorem copy_{nm}_long{bnd} (x c d e : Nat) (ps : List (Nat × Nat)) : ∃ n,
    steps n ⟨Q d e (P ps (Pc (c + 1) x (FC_{nm}{args}))), cons true (cons true blank), .A⟩ =
      some ⟨Fin d e (W ps d (G3_{nm}{args} x ({jf}) c)), cons true (cons true blank), .A⟩ := by
  obtain ⟨n1, h1⟩ := left_pass (Pc (c + 1) x (FC_{nm}{args})) ps d (R0 e)
  obtain ⟨n2, h2⟩ := loop {blist} (v2 + 1) 0 (WY x (U (c + 1) (LP ps d (R0 e)).1 (LP ps d (R0 e)).2))
  obtain ⟨n3, h3⟩ := right_pass (G3_{nm}{args} x ({jf}) c) ps d (R0 e)
  rw [show 0 + 2 * (v2 + 1) = {jf} by omega] at h2
  exact ⟨_, steps_seq trans (enter d e _) (steps_seq trans h1 (steps_seq trans (lu x (c + 1) _ _ _)
    (steps_seq trans (entry_{nm}{args} x _) (steps_seq trans h2 (steps_seq trans (exit3_{nm}{args} x _ c _ _)
      (steps_seq trans h3 (leave d e _)))))))⟩

/-- A whole copy tick of `{shape} | 1 . X . m1` (k = 1; X = 2x+2, m1 = 2e+2), from one right-end turn to the next. -/
theorem copy_{nm}_one{bnd} (x e : Nat) : ∃ n,
    steps n ⟨Q x e (FC_{nm}{args}), cons true (cons true blank), .A⟩ =
      some ⟨G1_{nm}{args} x ({jf}) e, cons true (cons true blank), .A⟩ := by
  obtain ⟨n2, h2⟩ := loop {blist} (v2 + 1) 0 (WY x (R0 e))
  rw [show 0 + 2 * (v2 + 1) = {jf} by omega] at h2
  exact ⟨_, steps_seq trans (enter x e _) (steps_seq trans (entry_{nm}{args} x _)
    (steps_seq trans h2 (exit1_{nm}{args} x _ e)))⟩
""")
    return parts, " ".join(map(str, g3.left)), " ".join(map(str, g1.left))


def subst_x(s, xk):
    return s.replace("(0101)^x ", f"(0101)^{xk} ")


def shapes_from_classify(path):
    txt = open(path).read().split("copy ticks:")[1].split("other")[0]
    out = OrderedDict()
    for ln in txt.strip().split("\n"):
        before = ln.split()[1]
        P = before[:before.rindex("|1.")]
        nums = list(map(int, re.findall(r"\d+", P)))
        seps = re.findall(r"[|.]", P)
        s = ""
        for j, n in enumerate(nums):
            s += "1" if n == 1 else ("e" if n % 2 == 0 else "o")
            if j < len(seps):
                s += seps[j]
        out[s] = out.get(s, 0) + 1
    with open(SHAPES, "w") as f:
        f.write("# P shapes of the copy ticks in the first 1e10 steps, and how many ticks have each (py/copyloop.py)\n")
        for s, n in out.items():
            f.write(f"{s} {n}\n")


DOC = """# The copy ticks

Generated by `py/copyloop.py` (see its docstring).  A copy tick reads `P | 1 . X . m1 . … . mk` (k odd, X and the
m's even).  The left pass ends on X; then the head goes back and forth between the left end and X.  After the
entry, which reworks P into a list `bs` of even blocks, the tape right of the head at the left end is
`Kj j (CS bs (X0 r Z))` = `1 (10)^(2j+2) 0 (10)^(2b1+2) … 0 (10)^(2bm+2) 0 0 (10)^(2r) Z`; `round` (seven local
pieces and two inductions on `bs`) moves two pairs of X into the first block, for every list `bs`, and `loop` is the
induction on r.  For each front shape of the run, `entry_*`, `exit3_*`, `exit1_*` are symbolic runs (a variable for
each block of P), and `copy_*_long` (k ≥ 3, any list of pairs) and `copy_*_one` (k = 1) are the whole tick, for
every X and every chain."""


SPLIT = 3_000_000   # a symbolic run longer than this many bytes is proved in segments (py/splitraw.py)
SPLIT_FIX = 100_000  # the same for the runs of a shape with a fixed block, whose tapes are long
SEGS_PER_FILE = 3   # segments (of 40 steps of the run each) per file
GROUP = 2_500_000   # at most about this many bytes of Lean per file of shapes (a bigger file runs Lean out of memory)


def write_lean(name, imports, parts, doc, split=None):
    """writes lean/<name>.lean; a symbolic run longer than SPLIT is proved in segments, written to files of their
    own (lean/<name>_p1.lean, …, each importing the one before) that the main file imports.  Returns the files,
    in the order to check them."""
    from splitraw import split_theorem
    files, segs, out = [], [], []
    for p in parts:
        if len(p) > (split or SPLIT) and "  have hn : " in p:
            ps = split_theorem(p, pieces=True)
            segs += ps[:-1]
            out.append(ps[-1])
        else:
            out.append(p)
    imp = imports
    for i in range(0, len(segs), SEGS_PER_FILE):
        pn = f"{name}_p{i // SEGS_PER_FILE + 1}"
        txt = rules_file(imp, NS, segs[i:i + SEGS_PER_FILE], f"# Segments of the long symbolic runs of `{name}.lean`\n\n"
                         "Generated by `py/copyloop.py` (`py/splitraw.py`).")
        txt = txt.replace("open TM\n", "open TM\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 4000000\n", 1)
        with open(os.path.join(HERE, "..", "lean", pn + ".lean"), "w") as f:
            f.write(txt)
        files.append(pn + ".lean")
        imp = pn
    parts = out
    txt = rules_file(imp, NS, parts, doc)
    txt = txt.replace("open TM\n", "open TM\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 4000000\n", 1)
    with open(os.path.join(HERE, "..", "lean", name + ".lean"), "w") as f:
        f.write(txt)
    return files + [name + ".lean"]


def gen():
    shapes = [ln.split()[0] for ln in open(SHAPES) if ln.strip() and not ln.startswith("#")]
    parts = [loop_defs()]
    for p in PIECES:
        parts += rule(*p)
    parts.append(LOOP_THMS)
    write_lean("Copy", "Chain", parts, DOC)
    done, table, groups = 0, [], [[]]
    for shape in shapes:
        if shape in SKIP:
            continue
        try:
            ps, info = gen_shape(shape)
        except Exception as e:
            print(f"{shape:28s} FAILED: {type(e).__name__}: {str(e)[:300]}")
            continue
        done += 1
        size = sum(len(x) for x in ps)
        if groups[-1] and sum(len(x) for g in groups[-1] for x in g[1]) + size > GROUP:
            groups.append([])
        groups[-1].append((shape, ps))
        j0, bs, r0, k, g3s, g1s = info
        table.append((shape, k, OFF.get(shape, {}), str(j0 + 2 * r0), g3s, g1s))
        print(f"{shape:28s} x -> x+{k}, blocks +{OFF.get(shape, {})}: j0 = {j0}, bs = {[str(b) for b in bs]}, r0 = {r0}")
    yparts, yg3, yg1 = gen_y()
    write_lean("CopyY", "Copy", yparts, f"# Copy ticks, front shape `{Y_SHAPE}`: the block Y between the two 1s is copied\n\n"
               "Generated by `py/copyloop.py` (`gen_y`); the loop is in `Copy.lean`.")
    table.append((Y_SHAPE, 0, {}, str(Lin(2, {"v2": 2})), yg3, yg1))
    done += 1
    print(f"{Y_SHAPE:28s} copies Y: j0 = 0, bs = [v0+2], r0 = v2+1")
    files = ["CopyY.lean"]
    for i, g in enumerate(groups, 1):
        names = ", ".join(f"`{sh}`" for sh, _ in g)
        files += write_lean(f"CopyS{i}", "Copy", [x for _, ps in g for x in ps],
                            f"# Copy ticks, front shapes {names}\n\nGenerated by `py/copyloop.py`; the loop is in "
                            "`Copy.lean`.", split=SPLIT_FIX if any(sh in FIX for sh, _ in g) else None)
    print(f"wrote lean/Copy.lean and {' '.join('lean/' + f for f in files)}: {done} shapes")
    with open(RESULTS, "w") as f:
        f.write("# P shape, k, offsets: copy_<shape>_* holds for X = 2(x+k)+2 and the block variables v + offset\n")
        for shape, k, off, jf, g3s, g1s in table:
            f.write(f"{shape} {k} {','.join(f'{v}+{a}' for v, a in sorted(off.items())) or '-'} {jf.replace(' ', '')}"
                    f" ; {g3s} ; {g1s}\n")
    check_sh = os.path.join(HERE, "..", "lean", "check.sh")
    txt = open(check_sh).read()
    txt = re.sub(r" Copy\.lean( Copy\w+\.lean)*", "", txt).rstrip("\n") + " Copy.lean " + " ".join(files) + "\n"
    with open(check_sh, "w") as f:
        f.write(txt)


def expand(s, env):
    out = []
    for t in s.split():
        if t.startswith("("):
            w, e = t[1:].split(")^")
            out += [int(ch) for ch in w] * parse_lin(e).subs(env)
        elif t != "0^inf":
            out += [int(ch) for ch in t]
    return out


def decode(bits):
    """the block list of a left tape at a right-end turn (as c/tick.c reads it)"""
    s = bits.index(1)
    out, start = "", s
    for p in range(s, len(bits) - 1):
        if bits[p] == bits[p + 1]:
            sep = p if bits[p] else p + 1
            out += str((sep - start) // 2) + ("|" if bits[p] else ".")
            start = sep + 1
    return out + str((len(bits) - start) // 2)


def check(path):
    """every copy tick of classify.txt: is it an instance of a theorem of lean/Copy.lean?"""
    res = {}
    for ln in open(RESULTS):
        if ln.startswith("#") or not ln.strip():
            continue
        head, g3s, g1s = ln.split(" ; ")
        shape, k, off, jf = head.split()
        res[shape] = (int(k), {} if off == "-" else {a.split("+")[0]: int(a.split("+")[1]) for a in off.split(",")},
                      jf, g3s, g1s.strip())
    txt = open(path).read().split("copy ticks:")[1].split("other")[0]
    n_ok = n = 0
    for ln in txt.strip().split("\n"):
        step, before = ln.split()[0], ln.split()[1]
        n += 1
        i = before.rindex("|1.")
        P, rest = before[:i], list(map(int, before[i + 3:].split(".")))
        nums, seps = list(map(int, re.findall(r"\d+", P))), re.findall(r"[|.]", P)
        shape = "".join(("1" if v == 1 else "eo"[v % 2]) + (seps[j] if j < len(seps) else "") for j, v in enumerate(nums))
        if shape not in res:
            print(f"{step}: {before[:60]}  front {shape}: not covered")
            continue
        k, off, jf, g3s, g1s = res[shape]
        vals = {}
        for j, v in enumerate(nums):
            if v != 1:
                vals[f"v{j}"] = (v - 2) // 2 if v % 2 == 0 else (v - 3) // 2
        X, chain = rest[0], rest[1:]
        ok = (X % 2 == 0 and (X - 2) // 2 >= k and all(vals[v] >= a for v, a in off.items())
              and all(vals[v] == a for v, a in FIX.get(shape, {}).items())
              and (len(chain) == 1 or (len(chain) % 2 == 1 and chain[0] >= 4)))
        thm = f"copy_{lean_name(shape)}_{'one' if len(chain) == 1 else 'long'}"
        # the theorem's end, read as a block list, against the run
        env = {v: vals[v] - off.get(v, 0) for v in vals}
        env["x"] = (X - 2) // 2 - k
        env["j"] = parse_lin(jf).subs(env)
        after = ln.split()[3]
        if len(chain) == 1:
            env["e"] = (chain[0] - 2) // 2
            pred = decode(expand(g1s, env))
            same = pred == after
        else:
            env["c"] = (chain[0] - 4) // 2
            pred = decode(expand(g3s, env))
            cut = max(pred.rfind("|"), pred.rfind("."))
            same = after.startswith(pred[:cut + 1])
        ok = ok and same
        print(f"{step}: front {shape}, X = {X}, {len(chain)} chain blocks: {thm} {'applies' if ok else 'DOES NOT APPLY'}"
              f"{'' if same else ' (end differs: ' + pred + ')'}")
        n_ok += ok
    print(f"{n_ok} of {n} copy ticks are instances of lean/Copy.lean")


if __name__ == "__main__":
    if len(sys.argv) > 2 and sys.argv[1] == "check":
        check(sys.argv[2])
    else:
        if len(sys.argv) > 1:
            shapes_from_classify(sys.argv[1])
        gen()
