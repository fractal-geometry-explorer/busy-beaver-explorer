"""Write lean/Family.lean for a machine of the block-list family: the round rule for every depth, by induction.

The file (namespace NS.FA) defines the machine's frame-A conjugate `FA.trans` (frames.py: the same five-state core
in the frame the analysis uses, written over the machine's own state type), proves the seven rules of a visit with
bbtools.symtm (PUSH, TURN, TAIL 1-4, POP; `*_raw` as the prover writes them, then restated in block-list form), and
proves `go_spec`: for every list of blocks and every depth, a clean visit does what the recursive function `go`
says, in `goT` steps.  Then (namespace NS) the conjugacy: the machine itself is FA.trans seen through `img`
(a renaming of the states, and for frames B and X the mirror image), proved step by step for every configuration,
so `go_spec`, the rounds and the halting question carry over (`steps_img`, `halts_iff`, `visit`).

usage: python3 gen_family_lean.py MACHINE NAMESPACE > lean/Family.lean
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
import frames  # noqa: E402
from bbtools.symtm import prove  # noqa: E402

B = {0: "false", 1: "true"}
T = {1: "1 0", 2: "1", 3: "1 0 0 1", 4: "1 0 1", 5: "1 1"}


def ctx(q, p):
    return f"L 1 0 0 (1000)^{q} {T[p]}"


RULES = [
    ("push_raw", "L A> 0 1 0 (1010)^k+1 1 1 0 R", "L 1 (0010)^k+1 A> 0 1 0 1 0 R"),
    ("turn_raw", "L A> 0 1 0 (1010)^k 1 0^inf", "L E> 1 0 1 0 1 (0101)^k 0 1 0^inf"),
    ("tail1_raw", f"{ctx('q+1', 1)} E> 1 0 (10)^x+1 1 R", "L 1 0 0 (1000)^q 1 A> 0 1 0 1 0 1 0 (10)^x+1 1 R"),
    ("tail2_raw", f"{ctx('q+1', 2)} E> 1 0 (10)^x+1 1 R", "L 1 0 0 (1000)^q 1 0 0 1 A> 0 1 0 1 0 (10)^x 1 R"),
    ("tail3_raw", f"{ctx('q', 3)} E> 1 0 (10)^x+1 1 R", "L 1 0 0 (1000)^q 1 0 1 A> 0 1 0 1 0 (10)^x 1 R"),
    ("tail4_raw", f"{ctx('q', 4)} E> 1 0 (10)^x+1 1 R", "L 1 0 0 (1000)^q 1 1 A> 0 1 0 1 0 (10)^x 1 R"),
    ("pop_raw", "L 1 0 0 (1000)^q 1 1 E> 1 0 X", "L E> 1 0 1 0 1 0 1 (0101)^q X"),
    ("birth_raw", "L A> 0 (1010)^k+2 1 0^inf",
     "L E> 1 0 1 0 1 (0101)^k 0 1 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 0^inf"),
]


def parse(m):
    t = {}
    for i, g in enumerate(m.split("_")):
        for y in (0, 1):
            s = g[3 * y:3 * y + 3]
            t[("ABCDEF"[i], y)] = None if s[2] == "-" else (int(s[0]), s[1], s[2])
    return t


def table_rows(m):
    t = parse(m)
    rows = []
    for s in "ABCDEF":
        for y in (0, 1):
            x = t[(s, y)]
            rhs = "none" if x is None else f"some ({B[x[0]]}, .{x[1]}, .{x[2]})"
            rows.append(f"  | .{s}, {B[y]} => {rhs}")
    return "\n".join(rows)


def generic():
    with open(os.path.join(HERE, "family_generic.lean")) as f:
        return f.read()


def raw_rules(fa):
    out = []
    for name, s, e in RULES:
        txt, fin = prove(fa, name, s, e, rotate=True, count_first=True, max_moves=10 ** 6, max_seg=40)
        out.append(txt)
    return "\n".join(out)


def conj(machine, fr, st):
    mp = frames.frame_map(fr)
    mirror = fr != "A"
    sig = "\n".join(f"  | .{a} => .{mp[a]}" for a in "ABCDEF")
    if mirror:
        img = "⟨tail c.r, cons (c.r 0) c.l, sigma c.st⟩"
        flip = "(fun d => match d with | .L => .R | .R => .L)"
        step_proof = """  obtain ⟨l, r, q⟩ := c
  cases q <;> cases h : r 0 <;> simp [TM.step, img, trans, FA.trans, sigma, h, cons_head_tail]"""
        init_proof = "  show (⟨blank, cons false blank, .A⟩ : Cfg St) = ⟨blank, blank, .A⟩\n  rw [cons_false_blank]"
    else:
        img = "⟨c.l, c.r, sigma c.st⟩"
        flip = "(fun d => d)"
        step_proof = """  obtain ⟨l, r, q⟩ := c
  cases q <;> cases h : r 0 <;> simp [TM.step, img, trans, FA.trans, sigma, h]"""
        init_proof = "  rfl"
    fr_txt = {"A": "frame A itself (`img` only renames nothing)",
              "B": "frame B: the mirror image of frame A, states renamed",
              "X": "frame X: the mirror image of frame A, states renamed",
              "G": "frame G: the mirror image of frame A, states renamed"}[fr]
    return f"""
/-! ## The machine is its frame-A conjugate seen through `img` ({fr_txt}) -/

/-- Frame-A state to this machine's state. -/
def sigma : St → St
{sig}

/-- A frame-A configuration as a configuration of this machine. -/
def img (c : Cfg St) : Cfg St := {img}

theorem hsig (q : St) (b : Bool) :
    trans (sigma q) b = (FA.trans q b).map (fun x => (x.1, {flip} x.2.1, sigma x.2.2)) := by
  cases q <;> cases b <;> rfl

theorem cons_head_tail (s : Tape) : cons (s 0) (tail s) = s := by
  funext n; cases n <;> rfl

/-- One step of the machine is one step of its frame-A conjugate. -/
theorem step_img (c : Cfg St) : TM.step trans (img c) = (TM.step FA.trans c).map img := by
{step_proof}

/-- Every run of the machine is a run of its frame-A conjugate. -/
theorem steps_img (n : Nat) (c : Cfg St) : TM.steps trans n (img c) = (TM.steps FA.trans n c).map img := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    unfold TM.steps
    rw [step_img]
    cases TM.step FA.trans c with
    | none => rfl
    | some c' => exact ih c'

/-- The run from blank tape is the image of the frame-A run from blank tape in state {st}. -/
theorem init_img : img ⟨blank, blank, .{st}⟩ = init := by
{init_proof}

/-- The machine halts from blank tape if and only if its frame-A conjugate halts from blank tape in state {st}. -/
theorem halts_iff : HaltsFromBlank ↔ TM.Halts FA.trans ⟨blank, blank, .{st}⟩ := by
  unfold HaltsFromBlank
  rw [← init_img]
  constructor
  · rintro ⟨n, d, h1, h2⟩
    rw [steps_img] at h1
    cases e : TM.steps FA.trans n ⟨blank, blank, .{st}⟩ with
    | none => rw [e] at h1; cases h1
    | some c' =>
      rw [e] at h1
      cases h1
      refine ⟨n, c', e, ?_⟩
      have := step_img c'
      rw [h2] at this
      cases e2 : TM.step FA.trans c' with
      | none => rfl
      | some _ => rw [e2] at this; cases this
  · rintro ⟨n, c', h1, h2⟩
    refine ⟨n, img c', ?_, ?_⟩
    · rw [steps_img, h1]; rfl
    · rw [step_img, h2]; rfl

/-- **The visit rule on this machine**: a clean visit to the block list `l` (frame A) is a run of this machine. -/
theorem visit (n : Nat) (l : List Nat) (h : FA.clean n l) (L : Tape) :
    steps (FA.goT n l) (img ⟨L, cons false (FA.enc l), .A⟩) =
      some (img ⟨L, cons true (cons false (FA.enc (FA.go n l))), .E⟩) := by
  have e := FA.go_spec n l h L
  show TM.steps trans _ _ = _
  rw [steps_img]
  exact congrArg (Option.map img) e
"""


def file_text(machine, ns):
    fr, fa, st = frames.info(machine)
    return f"""import Machine

/-!
# {machine}: the round rule of the nested block counter for every depth

Generated by `py/gen_family_lean.py` in the folder of the family's first machine
(holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---); do not edit by hand.

`FA.trans` is this machine's frame-A conjugate {fa} (frames.py); the run from blank tape starts there in state
{st}.  In frame A the right part of the tape is a list of plain blocks `(10)^b`, each followed by a 1, and the left part
a stack of spread blocks `1 0 0 (1000)^q T_p` (phase p = 1..5).  A *visit* to a list `l` starts with the head in A
on the 0 in front of the blocks and ends with the head back on that cell in E: PUSH spreads the first block, the
rest gets five visits with the four TAILs between them, POP makes the first block plain again; one block is a TURN.
`go_spec` proves it for every list and every depth (`clean` says the blocks are large enough and of the right
parity, a decidable condition); `visit` and `halts_iff` carry it over to the machine itself.
-/

namespace {ns}
namespace FA

open TM

/-- The frame-A conjugate of {machine}: {fa}. -/
def trans : St → Bool → Option (Bool × Dir × St)
{table_rows(fa)}

abbrev steps := TM.steps trans

/-! ## The seven rules as bbtools.symtm proves them -/

{raw_rules(fa)}
{generic().replace("@D1W@", B[parse(fa)[("D", 1)][0]])}
end FA

open TM
{conj(machine, fr, st)}
end {ns}
"""


if __name__ == "__main__":
    sys.stdout.write(file_text(sys.argv[1], sys.argv[2]))
