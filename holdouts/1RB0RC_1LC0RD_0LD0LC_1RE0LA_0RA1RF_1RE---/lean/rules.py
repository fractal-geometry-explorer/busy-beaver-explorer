"""Generate Rules.lean for MACHINE, one of the five machines 1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA{0RF,1RF}_{F}---: the
conversion sweeps and the rounds of the base-5 odometer (shared: they never reach state F), and the collision of two
`g4` gadgets across an empty block (different for each machine: the only place in these rules where F is used).

usage: python3 rules.py > Rules.lean
       python3 rules.py escape > Escape.lean      (halting corollaries of `trap` and `witness`)

The last two rules show the limits of any argument from the shapes of the tape alone.  `trap`: whatever the block
before it, the stretch `101` followed by a 1 (the transient gadget `10` meeting a gadget across an empty block) halts
in 4k+15 steps.  `witness`: a tape made only of the five regular gadgets, with every block of length >= 2, from which
the machine halts.  So a non-halting proof has to use relations between the block lengths, not just which gadgets occur.

Tapes are written left to right: `S>` is the head in state S on the next cell, `(w)^n` is n copies of the word w,
`0^inf` blank tape, L and R any tape.  Words: b = 1000; gadgets g0 = 1001, g1 = 1001100, g2 = 100110, g3 = 10011,
g4 = 10010, s = 0, X = 100.  An odometer round starts and ends with the head in D at the left end of the tape.
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "tools", "py"))
from bbtools.symtm import prove, rules_file, Config, run, Machine, Halted  # noqa: E402

M = "1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_1RE---"
NS = "H95904"

G = {"g0": "1 0 0 1", "g1": "1 0 0 1 1 0 0", "g2": "1 0 0 1 1 0", "g3": "1 0 0 1 1", "g4": "1 0 0 1 0", "s": "0"}

SHARED = [
    ("a_cross", "L A> (0100)^n R", "L (1010)^n A> R", "A turns `0100`s into `1010`s moving right."),
    ("b_cross", "L B> (1000)^n R", "L (0101)^n B> R", "B turns `1000`s into `0101`s moving right."),
    ("d_cross", "L D> (0001)^n R", "L (1010)^n D> R", "D turns `0001`s into `1010`s moving right."),
    ("e_cross", "L E> (0010)^n R", "L (0101)^n E> R", "E turns `0010`s into `0101`s moving right."),
    ("c_halve", "L (1010)^n C> 1 R", "L C> 1 (0100)^n R",
     "C, moving left, turns every two `10`s into one `1000` (shifted): the halving sweep."),
    ("c_sep", "L (1010)^n 1 C> 1 R", "L C> 1 (0100)^n 0 R",
     "The halving sweep crosses a block and the `1` that separates it from the next, which becomes a `0`."),
    ("round_g0", f"0^inf D> (1000)^k+3 {G['g0']} (1000)^y+3 R", f"0^inf D> (1000)^k+4 {G['g1']} (1000)^y+2 R",
     "Odometer round, first gadget g0 → g1: the left block gains one b, the block after the gadget loses one."),
    ("round_g1", f"0^inf D> (1000)^k+3 {G['g1']} (1000)^y+3 R", f"0^inf D> (1000)^k+4 {G['g2']} (1000)^y+3 R",
     "Odometer round, g1 → g2."),
    ("round_g2", f"0^inf D> (1000)^k+3 {G['g2']} (1000)^y+3 R", f"0^inf D> (1000)^k+4 {G['g3']} (1000)^y+3 R",
     "Odometer round, g2 → g3."),
    ("round_g4", f"0^inf D> (1000)^k+3 {G['g4']} (1000)^y+3 R", f"0^inf D> (1000)^k+5 {G['g0']} (1000)^y+2 R",
     "Odometer round, g4 → g0: the left block gains two b, the block after loses one."),
]
for g, h, dy in (("g0", "g1", 1), ("g1", "g2", 0), ("g2", "g3", 0), ("g4", "g0", 1), ("s", "g0", 0)):
    dl = {"g4": 4, "s": 2}.get(g, 3)
    SHARED.append((f"carry_{g}", f"0^inf D> (1000)^k+3 {G['g3']} (1000)^y+3 {G[g]} (1000)^z+3 R",
                   f"0^inf D> (1000)^k+4 {G['g4']} (1000)^y+{dl} {G[h]} (1000)^z+{3 - dy} R",
                   f"Odometer round with a carry: g3 → g4, and the next gadget {g} → {h}."))
SHARED += [
    ("reset1", f"0^inf D> (1000)^k+3 {G['g3']} (1000)^y+3 {G['g0']} 0^inf",
     f"0^inf D> 1 0 0 0 {G['g1']} (1000)^k+3 0 (1000)^y+4 {G['g0']} 0^inf",
     "A carry reaches the end of the tape: a full sweep right and back; every gadget becomes s and a new level "
     "`b g1` is born at the left."),
    ("reset2", f"0^inf D> (1000)^k+3 {G['g3']} (1000)^y+3 {G['g3']} (1000)^z+3 {G['g0']} 0^inf",
     f"0^inf D> 1 0 0 0 {G['g1']} (1000)^k+3 0 (1000)^y+4 0 (1000)^z+4 {G['g0']} 0^inf",
     "The same through two levels."),
]

COLLIDE = {
    "1RC": "0^inf D> 1 0 0 0 1 0 0 1 1 0 0 (1000)^k+5 1 0 0 (1000)^y+2 1 0 0 1 1 0 (1000)^z+3 R",
    "1RD": "0^inf D> (1000)^k+7 0 1 0 0 1 (1000)^y+1 1 0 0 1 1 0 (1000)^z+3 R",
    "0LD": "0^inf D> (1000)^k+6 1 0 0 1 0 (1000)^y+2 1 0 0 1 1 0 (1000)^z+3 R",
    "0RC": "0^inf D> (1000)^k+6 1 0 0 1 1 0 (1000)^y+2 1 0 0 1 1 (1000)^z+3 R",
    "1RE": "0^inf D> (1000)^k+6 1 0 0 1 1 0 (1000)^y+2 1 0 0 1 1 (1000)^z+3 R",
}
DOC = {
    "1RC": "a new level `b g1` is born and the two g4 become `X = 100`",
    "1RD": "the two g4 become `s g0` with an empty block between, and the left block gains four b",
    "0LD": "the two g4 merge into one g4, and the left block gains three b",
    "0RC": "the two g4 merge into a g2, and the next gadget advances (g2 → g3)",
    "1RE": "the two g4 merge into a g2, and the next gadget advances (g2 → g3)",
}


WITNESS = {
    "0RF_1RC": "6 g4 5 g4 2 g0 2 g0", "0RF_1RD": "6 g4 5 g4 2 g0 2 g0",
    "1RF_0LD": "6 g4 5 g3 2 s 2 g0", "1RF_0RC": "6 g4 5 g3 2 s 2 g0", "1RF_1RE": "6 g4 5 g3 2 s 2 g0",
}


def halt_end(start):
    """the configuration in which the run from `start` halts (symbolic run, shift rules on)"""
    last = []
    try:
        run(Machine.parse(M), Config.parse(start), lambda c: last.append(c.copy()) and False, max_moves=10 ** 6)
    except Halted:
        return last[-1]
    raise RuntimeError("no halt")


def escape_rules():
    trap = "0^inf D> (1000)^k+1 1 0 1 1 R"
    w = WITNESS[M[-10:-3]]
    ws = "0^inf D> " + " ".join(f"(1000)^{x}" if x.isdigit() else G[x] for x in w.split()) + " 0^inf"
    return [("trap", trap, halt_end(trap),
             "The trap: the stretch `101` after the first block, followed by a 1, ends in F reading a 1."),
            ("witness", ws, None,
             "A tape of regular gadgets with all blocks of length >= 2, `"
             + " ".join(f"b^{x}" if x.isdigit() else x for x in w.split()) + "`, ends in F reading a 1.")]


def main():
    f = M[-5:-3]
    f = M[-6:-3]
    rules = list(SHARED)
    rules.append(("collide", f"0^inf D> (1000)^k+3 {G['g4']} {G['g4']} (1000)^y+3 {G['g2']} (1000)^z+3 R",
                  COLLIDE[f], f"Two g4 with an empty block between, the next gadget g2 (state F is entered here, on "
                  f"a 0): {DOC[f]}."))
    esc = escape_rules()
    if sys.argv[1:] == ["escape"]:
        sys.stdout.write(escape_file(esc))
        return
    rules.append(esc[0])
    ths = [prove(M, name, a, b, doc=doc, max_seg=40)[0] for name, a, b, doc in rules]
    out = rules_file("Machine", NS, ths, f"Rules of {M}, generated by `rules.py`; do not edit by hand.")
    sys.stdout.write(out)


WSTEPS = {"0RF_1RC": 3722, "0RF_1RD": 3268, "1RF_0LD": 3275, "1RF_0RC": 3275, "1RF_1RE": 3275}
GB = {"g0": "1001", "g1": "1001100", "g2": "100110", "g3": "10011", "g4": "10010", "s": "0"}


def escape_file(rules):
    import re
    (name, a, b, doc), wit = rules
    th = prove(M, name, a, b, doc=doc, max_seg=40)[0]
    head = th[th.index("theorem"):th.index(":= by")]
    start = re.search(r"⟨(.*?)⟩ = some", head, re.S).group(1)
    w = WITNESS[M[-10:-3]]
    bits = "".join("1000" * int(x) if x.isdigit() else GB[x] for x in w.split())
    lst = "[" + ", ".join("true" if c == "1" else "false" for c in bits) + "]"
    pretty = " ".join(f"b^{x}" if x.isdigit() else x for x in w.split())
    n = WSTEPS[M[-10:-3]]
    return f"""import Rules
import Blank

/-! Halting corollaries for {M}, generated by `rules.py escape`; do not edit by hand.

`trap_halts`: from the head in D on `b^(k+1) 1 0 1 1`, whatever follows, the machine halts (rule `trap` of
`Rules.lean`): the transient gadget `10` meeting a gadget across an empty block is fatal.  `witness_halts`: from the
head in D on `{pretty}` (b = 1000; a tape of the regular gadgets only, every block of length >= 2) the machine
halts after {n:,} steps.  So the tape language "regular gadgets with arbitrary block lengths" contains halting
configurations, and no invariant on gadget shapes alone can prove that the machine does not halt. -/

namespace {NS}

open TM

/-- From the head in D on `b^(k+1) 1 0 1 1`, whatever follows, the machine halts. -/
theorem trap_halts (k : Nat) (R : Tape) :
    TM.Halts trans (⟨{start}⟩ : Config) :=
  ⟨_, _, trap k R, (step_none_iff _).2 ⟨rfl, rfl⟩⟩

/-- `n` list steps end in a configuration that halts. -/
def haltsAt (n : Nat) (c : FCfg St) : Bool :=
  match TM.fsteps trans n c with
  | some c' => (TM.fstep trans c').isNone
  | none => false

theorem halts_of_haltsAt {{n : Nat}} {{c : FCfg St}} (h : haltsAt n c = true) : TM.Halts trans c.toCfg := by
  unfold haltsAt at h
  split at h
  next c' e =>
    refine ⟨n, c'.toCfg, by rw [FCfg.steps_eq trans, e]; rfl, ?_⟩
    rw [FCfg.step_eq trans]
    cases e' : TM.fstep trans c' with
    | none => rfl
    | some _ => rw [e'] at h; cases h
  next => cases h

/-- The witness tape `{pretty}`, as a list of cells. -/
def witnessTape : List Bool := {lst}

/-- From the head in D on `{pretty}` (a tape of regular gadgets, every block of length >= 2) the machine halts,
after {n:,} steps; checked by Lean's kernel. -/
theorem witness_halts : TM.Halts trans (⟨blank, app witnessTape blank, .D⟩ : Config) :=
  halts_of_haltsAt (n := {n}) (c := ⟨[], witnessTape, .D⟩) (by decide +kernel)

end {NS}
"""


if __name__ == "__main__":
    main()
