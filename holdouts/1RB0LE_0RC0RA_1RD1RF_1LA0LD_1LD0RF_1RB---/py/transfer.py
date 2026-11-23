"""The copy rounds of 1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB--- are left-end ticks: a transfer theorem in Lean.

usage: python3 holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/py/transfer.py    # writes lean/Transfer.lean
       python3 holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/py/transfer.py check classify.txt
           runs every copy tick of classify.txt (`py/front.py classify`) on the machine and sorts each turn at X by
           the theorem of lean/Transfer.lean its round is an instance of

A left-end tick of a list `F | 3` (the last block 3, at the right end) and a round of a copy tick with front `F |`
(from one turn at the edge of X to the next) run the same *middle*: the head comes to the last separator of F in
state D, works inside F without ever reading the cells right of that separator, and comes back to it in state A.
`Mid L L'` says that for the tape L left of the separator (the blocks of F); the four end pieces below are symbolic
runs for every tape L (they never read it).  So `main_of_mid` and `round_of_mid` hold for every front: whatever the
middle does to F in the tick of `F | 3 -> F' | 4`, the copy round does too, and the round ends at the next turn
with F' as its front and one pair of X less.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools.symtm import rules_file, tokens, left_term, right_term  # noqa: E402
from tapeeq import rule, tape_eq, mirror  # noqa: E402

NS = "H103746"

DEFS = [
    ("Three", "(L : Tape)", "l", "L 1 1 0 1 0 1 0", "`L | 3`: the front, its last separator and the last block 3."),
    ("Four", "(L : Tape)", "l", "L 1 0 1 1 0 1 0 1 0 1 0", "`L 1 0 | 4`: the same after the tick."),
    ("Four4", "(L : Tape)", "l", "L 1 1 0 1 0 1 0 1 0", "`L | 4`."),
    ("M1", "", "r", "0 1 0 1 0 1 0 1 0^inf", "What the last block 3 leaves right of the separator."),
    ("XT", "(b : Nat) (L : Tape)", "l", "L 1 (1010)^b+1",
     "`L | (10)^(2b+2)`: the front and the pairs of X already passed, at a turn at the edge of X."),
    ("Y", "(b : Nat) (R : Tape)", "r", "(0101)^b+1 0 0 0 R", "What a copy round leaves right of the separator."),
    ("G", "(L : Tape)", "l", "L 1 0", "The front after a round: its last block one pair longer."),
    ("Yp", "(b : Nat) (R : Tape)", "r", "(0101)^b+1 0 R", "An even block after a separator 1, crossed to the left."),
    ("H", "(b : Nat) (L : Tape)", "l", "L 1 0 1 1 0 (1010)^b",
     "The same block after the middle: one pair moved to the block before it."),
    ("Od", "(b : Nat) (L : Tape)", "l", "L 1 1 0 (1010)^b+1", "`L | (10)^(2b+3)`: an odd block after a separator 1."),
    ("Od'", "(b : Nat) (L : Tape)", "l", "L 0 1 0 (1010)^b+1", "The same after the middle: `L . (10)^(2b+3)`."),
    ("E0", "(b : Nat)", "l", "0^inf 1 0 1 0 (1010)^b", "`(10)^(2b+2)`: an even first block, at the left end."),
    ("E0'", "(b : Nat)", "l", "0^inf 1 0 1 0 1 0 (1010)^b", "The same after the middle: `(10)^(2b+3)`."),
    ("O0", "(b : Nat)", "l", "0^inf 1 0 1 0 1 0 (1010)^b", "`(10)^(2b+3)`: an odd first block, at the left end."),
    ("O0'", "(b : Nat)", "l", "0^inf 1 0 1 0 1 0 1 1 0 1 0 (1010)^b",
     "The same after the middle: `3 | (10)^(2b+2)`."),
]

EQS = [  # name, left tape 1, left tape 2, vars, statement, doc
    ("G_H", "L 1 0 1 1 0 (1010)^b 1 0", "L 1 0 1 (1010)^b+1", ["b"], "G (H b L) = XT b (G L)",
     "A block that gave a pair to the block before it gets one back from the block after it."),
    ("G_Od'", "L 0 1 0 (1010)^b+1 1 0", "L 0 (1010)^b+2", ["b"], "G (Od' b L) = Ev b L",
     "`L | o` becomes `L . o+1`."),
    ("G_E0'", "0^inf 1 0 1 0 1 0 (1010)^b 1 0", "0^inf 1 0 1 0 (1010)^b+1", ["b"], "G (E0' b) = E0 (b + 1)",
     "An even first block grows by 2."),
    ("G_O0'", "0^inf 1 0 1 0 1 0 1 1 0 1 0 (1010)^b 1 0", "0^inf 1 0 1 0 1 0 1 1 0 (1010)^b+1", ["b"],
     "G (O0' b) = O1 b", "An odd first block o becomes `3 | o`."),
]

DEFS2 = [
    ("Ev", "(b : Nat) (L : Tape)", "l", "L 0 (1010)^b+2", "`L . (10)^(2b+4)`."),
    ("O1", "(b : Nat)", "l", "0^inf 1 0 1 0 1 0 1 1 0 (1010)^b+1", "`3 | (10)^(2b+3)`."),
]

PIECES = [
    ("main_in", "L 1 1 0 1 0 1 0 A> 1 1 0^inf", "L D> 1 0 1 0 1 0 1 0 1 0^inf", [],
     "⟨Three L, cons true (cons true blank), .A⟩", "⟨L, cons true M1, .D⟩",
     "The tick of `L | 3` from the right-end turn to the separator."),
    ("main_out", "L A> 0 0 1 0 1 0 1 0 1 0^inf", "L 1 0 1 1 0 1 0 1 0 1 0 A> 1 1 0^inf", [],
     "⟨L, cons false M1, .A⟩", "⟨Four L, cons true (cons true blank), .A⟩",
     "From the separator back to the right-end turn, with the last block 4."),
    ("copy_in", "L 1 (1010)^b+1 D> 1 0 0 R", "L D> 1 (0101)^b+1 0 0 0 R", ["b"],
     "⟨XT b L, cons true (cons false (cons false R)), .D⟩", "⟨L, cons true (Y b R), .D⟩",
     "A copy round from the turn at X to the separator."),
    ("copy_out", "L A> 0 (0101)^b+1 0 0 0 1 0 R", "L 1 0 1 (1010)^b+1 D> 1 0 0 R", ["b"],
     "⟨L, cons false (Y b (cons true (cons false R))), .A⟩",
     "⟨XT b (G L), cons true (cons false (cons false R)), .D⟩",
     "From the separator to the next turn at X, one pair of X further."),
    ("le", "L 1 (1010)^b+1 D> 1 R", "L D> 1 (0101)^b+1 0 R", ["b"],
     "⟨XT b L, cons true R, .D⟩", "⟨L, cons true (Yp b R), .D⟩",
     "The middle crosses an even block after a separator 1 to the left."),
    ("re", "L A> 0 (0101)^b+1 0 R", "L 1 0 1 1 0 (1010)^b A> 0 R", ["b"],
     "⟨L, cons false (Yp b R), .A⟩", "⟨H b L, cons false R, .A⟩",
     "And back to the right, passing one pair to the block before it."),
    ("mid_od", "L 1 1 0 (1010)^b+1 D> 1 R", "L 0 1 0 (1010)^b+1 A> 0 R", ["b"],
     "⟨Od b L, cons true R, .D⟩", "⟨Od' b L, cons false R, .A⟩",
     "The middle turns in an odd block after a separator 1, whatever is left of it."),
    ("mid_e0", "0^inf 1 0 1 0 (1010)^b D> 1 R", "0^inf 1 0 1 0 1 0 (1010)^b A> 0 R", ["b"],
     "⟨E0 b, cons true R, .D⟩", "⟨E0' b, cons false R, .A⟩", "The middle turns at the left end, after an even first block."),
    ("mid_o0", "0^inf 1 0 1 0 1 0 (1010)^b D> 1 R", "0^inf 1 0 1 0 1 0 1 1 0 1 0 (1010)^b A> 0 R", ["b"],
     "⟨O0 b, cons true R, .D⟩", "⟨O0' b, cons false R, .A⟩", "The middle turns at the left end, after an odd first block."),
]

THMS = """/-- The middle of a tick at the left end: from the last separator of the front in state D back to it in state A,
never reading the cells right of it. -/
def Mid (L L' : Tape) : Prop := ∀ R : Tape, ∃ n, steps n ⟨L, cons true R, .D⟩ = some ⟨L', cons false R, .A⟩

/-- The left-end tick of `F | 3`, from one right-end turn to the next, for any front with a middle. -/
theorem main_of_mid {L L' : Tape} (h : Mid L L') : ∃ n,
    steps n ⟨Three L, cons true (cons true blank), .A⟩ = some ⟨Four L', cons true (cons true blank), .A⟩ := by
  obtain ⟨n, hn⟩ := h M1
  exact ⟨_, steps_seq trans (main_in L) (steps_seq trans hn (main_out L'))⟩

/-- A copy round over the front `F |`, from one turn at the edge of X to the next, for any front with a middle:
the same middle as the tick of `F | 3`, so the same new front, and one pair `10` of X moved. -/
theorem round_of_mid {L L' : Tape} (h : Mid L L') (b : Nat) (R : Tape) : ∃ n,
    steps n ⟨XT b L, cons true (cons false (cons false (cons true (cons false R)))), .D⟩ =
      some ⟨XT b (G L'), cons true (cons false (cons false R)), .D⟩ := by
  obtain ⟨n, hn⟩ := h (Y b (cons true (cons false R)))
  exact ⟨_, steps_seq trans (copy_in b L _) (steps_seq trans hn (copy_out b L' R))⟩

/-- The transfer: a middle proved for one front gives both its left-end tick and its copy round. -/
theorem transfer {L L' : Tape} (h : Mid L L') :
    (∃ n, steps n ⟨Three L, cons true (cons true blank), .A⟩ = some ⟨Four L', cons true (cons true blank), .A⟩) ∧
    ∀ (b : Nat) (R : Tape), ∃ n, steps n ⟨XT b L, cons true (cons false (cons false (cons true (cons false R)))), .D⟩ =
      some ⟨XT b (G L'), cons true (cons false (cons false R)), .D⟩ :=
  ⟨main_of_mid h, round_of_mid h⟩

/-- Rounds in a row: a list of fronts, each the middle's result of the one before, grown by a pair. -/
def Mids : Tape → List Tape → Prop
  | _, [] => True
  | L, L' :: Ls => Mid L L' ∧ Mids (G L') Ls

/-- The last front of such a list. -/
def lastF : Tape → List Tape → Tape
  | L, [] => L
  | _, L' :: Ls => lastF (G L') Ls

/-- k = |Ls| copy rounds in a row move k pairs of X. -/
theorem rounds_of_mids : ∀ (Ls : List Tape) (L : Tape), Mids L Ls → ∀ (b : Nat) (R : Tape), ∃ n,
    steps n ⟨XT b L, cons true (cons false (cons false (rep Ls.length [true, false] R))), .D⟩ =
      some ⟨XT b (lastF L Ls), cons true (cons false (cons false R)), .D⟩ := by
  intro Ls
  induction Ls with
  | nil => intro L _ b R; exact ⟨0, rfl⟩
  | cons L' Ls ih =>
    intro L h b R
    obtain ⟨n1, h1⟩ := round_of_mid h.1 b (rep Ls.length [true, false] R)
    obtain ⟨n2, h2⟩ := ih (G L') h.2 b R
    exact ⟨_, steps_seq trans h1 h2⟩
"""

CASES = [  # name, front before (as a left tape of b, L), its middle, the new front, block notation, doc
    ("od", "Od b L", "Od' b L", "Ev b L", "(b : Nat) (L : Tape)", "b L", "G_Od' b L",
     "`L | o | e1 | … | ek |`  ->  `L . o+1 | e1 | … | ek |`, whatever L is"),
    ("e0", "E0 b", "E0' b", "E0 (b + 1)", "(b : Nat)", "b", "G_E0' b",
     "`e | e1 | … | ek |`  ->  `e+2 | e1 | … | ek |`, e the first block"),
    ("o0", "O0 b", "O0' b", "O1 b", "(b : Nat)", "b", "G_O0' b",
     "`o | e1 | … | ek |`  ->  `3 | o | e1 | … | ek |`, o the first block"),
]


def case_thms():
    out = []
    for nm, f, m, g, bnd, args, geq, doc in CASES:
        out.append(f"""/-- The middle for the fronts {doc.split("  ->")[0]} (e1 … ek even, any k). -/
theorem midF_{nm} {bnd} (bs : List Nat) : Mid (XTs bs ({f})) (Hs bs ({m})) :=
  mid_evens bs (fun R => ⟨_, mid_{nm} {args} R⟩)

/-- The copy round over the front {doc}: from one turn at X to the next. -/
theorem round_{nm} {bnd} (bs : List Nat) (c : Nat) (R : Tape) : ∃ n,
    steps n ⟨XT c (XTs bs ({f})), cons true (cons false (cons false (cons true (cons false R)))), .D⟩ =
      some ⟨XT c (XTs bs ({g})), cons true (cons false (cons false R)), .D⟩ := by
  have h := round_of_mid (midF_{nm} {args} bs) c R
  rwa [G_Hs, {geq}] at h

/-- The left-end tick of the same front followed by the last block 3: {doc.replace("|`  ->", "| 3`  ->").replace("ek |`,", "ek | 4`,").replace("ek |`", "ek | 4`")}. -/
theorem tick3_{nm} {bnd} (bs : List Nat) : ∃ n,
    steps n ⟨Three (XTs bs ({f})), cons true (cons true blank), .A⟩ =
      some ⟨Four4 (XTs bs ({g})), cons true (cons true blank), .A⟩ := by
  have h := main_of_mid (midF_{nm} {args} bs)
  rwa [four_eq, G_Hs, {geq}] at h
""")
    return "\n".join(out)

THMS2 = """theorem four_eq (L : Tape) : Four L = Four4 (G L) := rfl

/-- An even block after a separator 1 is passive: the middle crosses it, runs on what is left of it, and comes back. -/
theorem mid_even {L L' : Tape} (h : Mid L L') (b : Nat) : Mid (XT b L) (H b L') := by
  intro R
  obtain ⟨n, hn⟩ := h (Yp b R)
  exact ⟨_, steps_seq trans (le b L R) (steps_seq trans hn (re b L' R))⟩

/-- Even blocks after separators 1, the first one of the list nearest the left end. -/
def XTs : List Nat → Tape → Tape
  | [], L => L
  | b :: bs, L => XTs bs (XT b L)
/-- The same blocks after the middle. -/
def Hs : List Nat → Tape → Tape
  | [], L => L
  | b :: bs, L => Hs bs (H b L)

/-- Any number of even blocks after separators 1 at the end of the front are passive. -/
theorem mid_evens : ∀ (bs : List Nat) {L L' : Tape}, Mid L L' → Mid (XTs bs L) (Hs bs L') := by
  intro bs
  induction bs with
  | nil => intro L L' h; exact h
  | cons b bs ih => intro L L' h; exact ih (mid_even h b)

/-- After the round (or the tick) the passive blocks are what they were. -/
theorem G_Hs : ∀ (bs : List Nat) (L : Tape), G (Hs bs L) = XTs bs (G L) := by
  intro bs
  induction bs with
  | nil => intro L; rfl
  | cons b bs ih => intro L; simp only [Hs, XTs]; rw [ih, G_H]
"""


# ---------------------------------------------------------------- more turn shapes, generated
# a shape: '^' (the left end) or 'L' (any tape), then blocks e (even), o (odd >= 3), 1, each after its separator
# ('|' or '.'; none for a first block after '^'); the front is the shape followed by passive even blocks.
BASES = ["L|o.e", "^o.e", "L.e.e", "^e.e", "L|1", "L|e.e", "^e.e.o", "^e.o", "L|o|o.o", "^o|1.o", "L|1|o.e.o",
         "L|1.e", "^o|o.o", "L|o|o.e.e.e.o", "^o|o.e.o", "^e|e.o", "L|e.e.o", "L|o|o.e.o", "^o|1.e.e.o"]


def base_tokens(shape):
    import re as _re
    parts = _re.findall(r"([|.]?)([eo1])", shape[1:])
    return parts


def base_start(shape, off):
    """off: v -> k (the block variable is v + k) or (k,) (the block variable is the number k)"""
    out = ["L"] if shape[0] == "L" else ["0^inf"]
    vs = []
    for i, (sep, k) in enumerate(base_tokens(shape)):
        if sep:
            out.append("1" if sep == "|" else "0")
        if k == "1":
            out.append("1 0")
            continue
        v = f"v{i}"
        o = off.get(v, 0)
        if isinstance(o, tuple):
            rep = f"(1010)^{o[0]}"
        else:
            vs.append(v)
            rep = f"(1010)^{v}+{o}" if o else f"(1010)^{v}"
        out.append(("1 0 1 0 " if k == "e" else "1 0 1 0 1 0 ") + rep)
    return " ".join(out), vs


def off_str(off):
    return ", ".join(f"{v} = {o[0]}" if isinstance(o, tuple) else f"{v} ≥ {o}" for v, o in sorted(off.items())) or "-"


def off_name(off):
    return "".join(f"_{v}eq{o[0]}" if isinstance(o, tuple) else "" for v, o in sorted(off.items()))


def base_doc(shape):
    return shape.replace("^", "").replace("L", "L ").replace("|", " | ").replace(".", " . ").strip()


def gen_base(shape, off=None, depth=0, dot=False):
    """the cases of a shape: on a split of a block variable v (v + k), the case v = k and the case v ≥ k + 1"""
    from bbtools.symtm import Config, run, NeedSplit, TouchContext, Ctx
    from bbtools.machine import Machine
    import re as _re
    m = Machine.parse("1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---")
    off = dict(off or {})
    if depth > 8:
        raise RuntimeError(f"{shape}: too many splits")
    if True:
        st, vs = base_start(shape, off)
        c = Config.parse(st + (" D> 0 R" if dot else " D> 1 R"))
        out_state, out_sym = (1, 1) if dot else (0, 0)
        try:
            run(m, c, lambda c: c.state == out_state and len(c.right) == 2 and c.right[0] == out_sym
                and isinstance(c.right[1], Ctx), max_moves=200000, rotate=True)
        except NeedSplit as e:
            mm = _re.search(r"\(\w+\)\^(v\d+)", str(e))
            if not mm:
                raise
            v = mm.group(1)
            k = off.get(v, 0)
            return (gen_base(shape, {**off, v: (k,)}, depth + 1, dot)
                    + gen_base(shape, {**off, v: k + 1}, depth + 1, dot))
        end = str(c)
        left_end = end.split(" B> " if dot else " A> ")[0]
        if dot:
            return [(dot_parts(shape, off, st, vs, left_end), off)]
        nm = "b_" + shape.replace("^", "Z").replace("|", "I").replace(".", "_") + off_name(off)
        args = (" ".join(vs) + (" L" if shape[0] == "L" else "")).strip()
        bnd = (f"({' '.join(vs)} : Nat)" if vs else "") + (" (L : Tape)" if shape[0] == "L" else "")
        bnd = bnd.strip()
        F, F2 = "S_" + nm, "S'_" + nm
        defs = (f"/-- The front `{base_doc(shape)}` ({off_str(off)}). -/\n"
                f"def {F} {bnd} : Tape := {left_term(tokens(st))}\n"
                f"/-- The same after the middle. -/\ndef {F2} {bnd} : Tape := {left_term(tokens(left_end))}\n")
        parts = [defs]
        parts += rule("mid_" + nm, st + " D> 1 R", left_end + " A> 0 R", vs,
                      f"⟨{F} {args}, cons true R, .D⟩", f"⟨{F2} {args}, cons false R, .A⟩",
                      f"The middle for the front `{base_doc(shape)}`.")
        parts.append(f"""/-- The copy round over the front `{base_doc(shape)} | e1 | … | ek |`. -/
theorem round_{nm} {bnd} (bs : List Nat) (c : Nat) (R : Tape) : ∃ n,
    steps n ⟨XT c (XTs bs ({F} {args})), cons true (cons false (cons false (cons true (cons false R)))), .D⟩ =
      some ⟨XT c (XTs bs (G ({F2} {args}))), cons true (cons false (cons false R)), .D⟩ := by
  have h := round_of_mid (mid_evens bs (fun R => ⟨_, mid_{nm} {args} R⟩)) c R
  rwa [G_Hs] at h

/-- The left-end tick of `{base_doc(shape)} | e1 | … | ek | 3`. -/
theorem tick3_{nm} {bnd} (bs : List Nat) : ∃ n,
    steps n ⟨Three (XTs bs ({F} {args})), cons true (cons true blank), .A⟩ =
      some ⟨Four4 (XTs bs (G ({F2} {args}))), cons true (cons true blank), .A⟩ := by
  have h := main_of_mid (mid_evens bs (fun R => ⟨_, mid_{nm} {args} R⟩))
  rwa [four_eq, G_Hs] at h
""")
        return [(parts, off)]


def dot_parts(shape, off, st, vs, left_end):
    nm = "d_" + shape.replace("^", "Z").replace("|", "I").replace(".", "_") + off_name(off)
    args = (" ".join(vs) + (" L" if shape[0] == "L" else "")).strip()
    bnd = ((f"({' '.join(vs)} : Nat)" if vs else "") + (" (L : Tape)" if shape[0] == "L" else "")).strip()
    F, F2 = "S_" + nm, "S'_" + nm
    parts = [f"/-- The front `{base_doc(shape)} .` ({off_str(off)}). -/\n"
             f"def {F} {bnd} : Tape := {left_term(tokens(st))}\n"
             f"/-- The same after the middle. -/\ndef {F2} {bnd} : Tape := {left_term(tokens(left_end))}\n"]
    parts += rule("dmid_" + nm, st + " D> 0 R", left_end + " B> 1 R", vs,
                  f"⟨{F} {args}, cons false R, .D⟩", f"⟨{F2} {args}, cons true R, .B⟩",
                  f"The middle for the front `{base_doc(shape)} .`.")
    parts.append(f"""/-- The copy round over the front `{base_doc(shape)} .` (a first round of a copy tick). -/
theorem round_{nm} {bnd} (c : Nat) (R : Tape) : ∃ n,
    steps n ⟨XTd c ({F} {args}), cons true (cons false (cons false (cons true (cons false R)))), .D⟩ =
      some ⟨XTe c ({F2} {args}), cons true (cons false (cons false R)), .D⟩ :=
  round_of_dmid (fun R => ⟨_, dmid_{nm} {args} R⟩) c R

/-- The left-end tick of `{base_doc(shape)} . 3`. -/
theorem tickd3_{nm} {bnd} : ∃ n,
    steps n ⟨ThreeD ({F} {args}), cons true (cons true blank), .A⟩ =
      some ⟨FourD ({F2} {args}), cons true (cons true blank), .A⟩ :=
  main_of_dmid (fun R => ⟨_, dmid_{nm} {args} R⟩)
""")
    return parts


DOT_BASES = ["L|e", "L|o", "L.e", "L|1", "^e", "^o"]

DOT_DEFS = [
    ("ThreeD", "(L : Tape)", "l", "L 0 1 0 1 0 1 0", "`L . 3`."),
    ("FourD", "(L : Tape)", "l", "L 0 1 0 1 0 1 0 1 0 1 0", "`L 0 (10)^5`: the same after the tick."),
    ("XTd", "(c : Nat) (L : Tape)", "l", "L 0 (1010)^c+1", "`L . (10)^(2c+2)`: a turn at X, the front ending in a 0."),
    ("XTe", "(c : Nat) (L : Tape)", "l", "L 0 1 0 (1010)^c+1", "The next turn at X after a round over such a front."),
    ("XTo", "(c : Nat) (L : Tape)", "l", "L 1 1 0 (1010)^c+1", "`L | (10)^(2c+3)`: a turn at X, an odd number of pairs."),
]

DOT_PIECES = [
    ("main_in_d", "L 0 1 0 1 0 1 0 A> 1 1 0^inf", "L D> 0 0 1 0 1 0 1 0 1 0^inf", [],
     "⟨ThreeD L, cons true (cons true blank), .A⟩", "⟨L, cons false M1, .D⟩",
     "The tick of `L . 3` from the right-end turn to the separator."),
    ("main_out_d", "L B> 1 0 1 0 1 0 1 0 1 0^inf", "L 0 1 0 1 0 1 0 1 0 1 0 A> 1 1 0^inf", [],
     "⟨L, cons true M1, .B⟩", "⟨FourD L, cons true (cons true blank), .A⟩", "From the separator to the right-end turn."),
    ("copy_in_d", "L 0 (1010)^c+1 D> 1 0 0 R", "L D> 0 (0101)^c+1 0 0 0 R", ["c"],
     "⟨XTd c L, cons true (cons false (cons false R)), .D⟩", "⟨L, cons false (Y c R), .D⟩",
     "A copy round over a front ending in a 0, from the turn at X to the separator."),
    ("copy_out_d", "L B> 1 (0101)^c+1 0 0 0 1 0 R", "L 0 1 0 (1010)^c+1 D> 1 0 0 R", ["c"],
     "⟨L, cons true (Y c (cons true (cons false R))), .B⟩", "⟨XTe c L, cons true (cons false (cons false R)), .D⟩",
     "From the separator to the next turn at X, one pair of X further."),
    ("round_odd", "L 1 1 0 (1010)^c+1 D> 1 0 0 1 0 R", "L 0 (1010)^c+2 D> 1 0 0 R", ["c"],
     "⟨XTo c L, cons true (cons false (cons false (cons true (cons false R)))), .D⟩",
     "⟨XTd (c + 1) L, cons true (cons false (cons false R)), .D⟩",
     "A round with an odd number of pairs after the front's last separator 1, for every front: it never reads the "
     "front, turns the separator into a 0, and moves one pair of X."),
]

DOT_THMS = """/-- The middle for a front ending in a separator 0: from that separator in state D back to it in state B. -/
def DMid (L L' : Tape) : Prop := ∀ R : Tape, ∃ n, steps n ⟨L, cons false R, .D⟩ = some ⟨L', cons true R, .B⟩

/-- The left-end tick of `F . 3`, for any front with such a middle. -/
theorem main_of_dmid {L L' : Tape} (h : DMid L L') : ∃ n,
    steps n ⟨ThreeD L, cons true (cons true blank), .A⟩ = some ⟨FourD L', cons true (cons true blank), .A⟩ := by
  obtain ⟨n, hn⟩ := h M1
  exact ⟨_, steps_seq trans (main_in_d L) (steps_seq trans hn (main_out_d L'))⟩

/-- The copy round over a front `F .`, for any front with such a middle: the same middle as the tick of `F . 3`. -/
theorem round_of_dmid {L L' : Tape} (h : DMid L L') (c : Nat) (R : Tape) : ∃ n,
    steps n ⟨XTd c L, cons true (cons false (cons false (cons true (cons false R)))), .D⟩ =
      some ⟨XTe c L', cons true (cons false (cons false R)), .D⟩ := by
  obtain ⟨n, hn⟩ := h (Y c (cons true (cons false R)))
  exact ⟨_, steps_seq trans (copy_in_d c L _) (steps_seq trans hn (copy_out_d c L' R))⟩
"""


# ---------------------------------------------------------------- the check against the run
TABLE = {(s, y): (int(r[3 * y]), 1 if r[3 * y + 1] == "R" else -1, ord(r[3 * y + 2]) - 65)
         for s, r in enumerate("1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---".split("_")) for y in range(2)
         if r[3 * y] != "-"}


def build(lst):
    import re as _re
    tape = []
    for n, sep in _re.findall(r"(\d+)([|.]?)", lst):
        tape += [1, 0] * int(n)
        tape += [1] if sep == "|" else [0] if sep == "." else []
    return tape + [1, 1]


def x_turns(lst):
    """the turns at the edge of X of the copy tick of the list (from its right-end turn): (cell, tape)"""
    i = lst.rindex("|1.")
    xpos = len(build(lst[:i + 3])) - 2
    nx = int(lst[i + 3:].split(".")[0])
    tape = build(lst)
    tp = dict(enumerate(tape))
    h, st, d, hi, out = len(tape) - 2, 0, -1, len(tape) - 1, []
    while True:
        w, D, s2 = TABLE[(st, tp.get(h, 0))]
        tp[h] = w
        h0, h, st = h, h + D, s2
        hi = max(hi, h)
        if d == 1 and D == -1 and h0 == hi:
            return out
        if d == 1 and D == -1 and xpos - 4 <= h0 < xpos + 2 * nx:
            out.append((h0, dict(tp)))
        d = D


def front_at(tp, h0):
    """the blocks and separators left of the turn, the front up to its last separator 1, and the pairs after it"""
    lo = min(k for k, v in tp.items() if v)
    bits = [tp.get(k, 0) for k in range(lo, h0 + 1)]
    blocks, start = [], 0
    for p in range(len(bits) - 1):
        if bits[p] == bits[p + 1]:
            sep = p if bits[p] else p + 1
            blocks.append(((sep - start) // 2, "|" if bits[p] else "."))
            start = sep + 1
    m = (len(bits) - start - 1) // 2
    # the turn reads L | (10)^m D> 1 0 0 1 0 ...: the round's start configuration (XT, for m even)
    if not (bits[start:] == [1, 0] * (m + 1) and [tp.get(h0 + k, 0) for k in (1, 2, 3)] == [0, 1, 0]):
        return [], None
    return blocks, m


def kind(n):
    return "1" if n == 1 else "eo"[n % 2]


def round_theorem(blocks, m):
    """the theorem of lean/Transfer.lean whose round this is, or why none is"""
    if m is None:
        return "the last turn: no pair of X left (the exit)"
    seps = [None] + [sp for _, sp in blocks[:-1]]
    bl = [(n, seps[i]) for i, (n, _) in enumerate(blocks)]
    if blocks and blocks[-1][1] == "|" and m % 2:
        return "round_odd"
    if not blocks or m % 2:
        return "no theorem: odd number of pairs after a front ending in a 0"
    if blocks[-1][1] == ".":
        for k in range(1, len(bl) + 1):
            shape = ("^" if k == len(bl) else "L") + "".join((sp or "") + kind(n) for n, sp in bl[-k:])
            if shape in DOT_BASES:
                return f"round_d_<{shape}>"
        return "no theorem: front ending in a 0"
    i = len(bl) - 1
    while i >= 1 and bl[i][0] % 2 == 0 and bl[i][0] >= 2 and bl[i][1] == "|":
        i -= 1
    core = bl[:i + 1]
    if i == 0 and core[0][0] >= 2:
        return "round_e0" if core[0][0] % 2 == 0 else "round_o0"
    if core[-1][1] == "|" and core[-1][0] % 2 and core[-1][0] >= 3:
        return "round_od"
    for k in range(1, len(core) + 1):
        shape = ("^" if k == len(core) else "L") + "".join((sp or "") + kind(n) for n, sp in core[-k:])
        if shape in BASES:
            return f"round_b_<{shape}>"
    return f"no theorem: turn shape {('^' + ''.join((sp or '') + kind(n) for n, sp in core))}"


def check(path):
    from collections import Counter
    txt = open(path).read().split("copy ticks:")[1].split("other")[0]
    cnt, n = Counter(), 0
    for ln in txt.strip().split("\n"):
        before = ln.split()[1]
        i = before.rindex("|1.")
        rest = before[i + 3:].split(".")
        lst = before[:i] + "|1." + str(min(int(rest[0]), 60)) + "." + ".".join(rest[1:])   # the same rounds
        for h0, tp in x_turns(lst):
            cnt[round_theorem(*front_at(tp, h0))] += 1
            n += 1
    ok = sum(v for k, v in cnt.items() if k.startswith("round"))
    for k, v in sorted(cnt.items(), key=lambda kv: -kv[1]):
        print(f"{v:6d}  {k}")
    print(f"{ok} of {n} turns at X in the {len(txt.strip().splitlines())} copy ticks are rounds of a theorem of "
          f"lean/Transfer.lean")


def defs(table=None):
    out = []
    for nm, b, kind, s, doc in (table or DEFS):
        term = right_term(tokens(s)) if kind == "r" else left_term(tokens(s))
        out.append(f"/-- {doc} -/\ndef {nm} {b} : Tape := {term}\n".replace("def M1  :", "def M1 :"))
    return "".join(out)


def main():
    parts = [defs()]
    for p in PIECES:
        parts += rule(*p)
    parts.append(THMS)
    parts.append(defs(DEFS2))
    for nm, a, b, vs, stmt, doc in EQS:
        parts.append(tape_eq(nm + "_raw", mirror(tokens(a)), mirror(tokens(b)), vs, doc=doc, ctxs=["L"]))
        binders = f"({' '.join(vs)} : Nat)" + (" (L : Tape)" if "L" in stmt else "")
        parts.append(f"/-- {doc} -/\ntheorem {nm} {binders} : {stmt} := {nm}_raw {' '.join(vs)}{' L' if 'L' in stmt else ''}\n")
    parts.append(THMS2)
    parts.append(case_thms())
    for shape in BASES:
        try:
            cases = gen_base(shape)
        except Exception as e:
            print(f"{shape:16s} FAILED: {type(e).__name__}: {str(e)[:200]}")
            continue
        for ps, off in cases:
            parts += ps
        print(f"{shape:16s} ok: {'; '.join(off_str(o) for _, o in cases)}")
    parts.append(defs(DOT_DEFS))
    for p in DOT_PIECES:
        parts += rule(*p)
    parts.append(DOT_THMS)
    for shape in DOT_BASES:
        try:
            cases = gen_base(shape, dot=True)
        except Exception as e:
            print(f"{shape:16s} . FAILED: {type(e).__name__}: {str(e)[:200]}")
            continue
        for ps, off in cases:
            parts += ps
        print(f"{shape + ' .':16s} ok: {'; '.join(off_str(o) for _, o in cases)}")
    doc = ("# Copy rounds are left-end ticks\n\n" + __doc__.split("\n\n", 2)[2].strip()
           + "\n\nGenerated by `py/transfer.py` (symbolic runs: `tools/py/bbtools/symtm.py`).")
    txt = rules_file("Machine", NS, parts, doc)
    txt = txt.replace("open TM\n", "open TM\n\nset_option maxRecDepth 100000\n", 1)
    with open(os.path.join(HERE, "..", "lean", "Transfer.lean"), "w") as f:
        f.write(txt)
    print("wrote lean/Transfer.lean")


if __name__ == "__main__":
    if sys.argv[1:2] == ["check"]:
        check(sys.argv[2])
    else:
        main()
