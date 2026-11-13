"""Ticks of 1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB--- over chains of even blocks of any length, proved in Lean.

usage: python3 holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/py/chain.py     writes lean/Chain.lean

The families `x | a . b1 . c1 . … . d . e` (all blocks even) and `x | p | a . b1 . c1 . … . d . e` (p, a odd, the
rest even) of the README: one tick is five kinds of piece,
each a symbolic run between tape forms with unknown tape L, R around it (`bbtools.symtm.prove`, the end tape
rebracketed by `py/tapeeq.py`):

    enter  A crosses the last block e leftwards                   ⟨Q d e L, 1 1 0^inf, A⟩ -> ⟨Rot d L, 010 R0 e, D⟩
    lu     one pair of blocks (b, c) on the way left               ⟨Rot d (Pc c b L), 010 R, D⟩ -> ⟨Rot b L, 010 (U c d R), D⟩
    turn   at the separator 1 before block a                        ⟨Rot b (T a L), 010 R, D⟩ -> ⟨T' a L, A0100 b R, A⟩
    turn_oo  at `| p | a` with p, a odd                             ⟨Rot b (To p a L), 010 R, D⟩ -> ⟨To' p a L, A0100 b R, A⟩
    ru     one pair on the way right                                ⟨L, A0100 b (U c d R), A⟩ -> ⟨V b c L, A0100 d R, A⟩
    leave  the last block, back at the right end                    ⟨L, A0100 d (R0 e), A⟩ -> ⟨Fin d e L, 1 1 0^inf, A⟩

The Lean file then proves the passes over any list of pairs by induction on the list (`left_pass`, `right_pass`)
and chains them into `tick_chain` and `tick_chain_oo`.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools.symtm import rules_file, tokens, left_term, right_term  # noqa: E402
from tapeeq import rule  # noqa: E402

NS = "H103746"

# tape pieces (left pieces start with their outer context, right pieces end with it)
Q = "L 0 (1010)^d+1 0 (1010)^e+1"
ROT = "L 0 1 0 1 (0101)^d"
PC = "L 0 (1010)^b+1 0 (1010)^c+1"
U = "1 0 (1010)^c 0 1 0 1 0 1 0 (1010)^d 0 R"
T = "L 1 (1010)^a+1"
T2 = "L 0 1 (0101)^a 0 1 0 1 1 0"
A0100 = "(0101)^b 0 1 0 0 R"
V = "L (1010)^b 1 0 1 0 1 1 (0101)^c 0 1 1 0"
R0 = "(1010)^e+1 1 0^inf"
FIN = "L (1010)^d 1 0 1 0 1 1 (0101)^e 0 1 0 1 0"
TO = "L 1 1 0 (1010)^p 1 0 1 0 1 1 0 (1010)^a 1 0 1 0"
TO2 = "L 0 1 0 1 (0101)^p 0 1 0 1 0 1 1 (0101)^a 0 1 0 1 1 0"


def lt(s):
    return left_term(tokens(s))


def rt(s):
    return right_term(tokens(s))


def defs():
    return f"""set_option maxRecDepth 100000

/-- `L 0 (10)^(2d+2) 0 (10)^(2e+2)`: the last two blocks, before a tick. -/
def Q (d e : Nat) (L : Tape) : Tape := {lt(Q)}
/-- `L 0 1 0 1 (0101)^d`: a block during the left pass. -/
def Rot (d : Nat) (L : Tape) : Tape := {lt(ROT)}
/-- `L 0 (10)^(2b+2) 0 (10)^(2c+2)`: a pair of blocks with their separators 0. -/
def Pc (c b : Nat) (L : Tape) : Tape := {lt(PC)}
/-- A list of pairs of blocks, the head of the list nearest to the head of the machine. -/
def P : List (Nat × Nat) → Tape → Tape
  | [], L => L
  | (c, b) :: ps, L => Pc c b (P ps L)
/-- What the left pass leaves on the right for a pair. -/
def U (c d : Nat) (R : Tape) : Tape := {rt(U)}
/-- `L 1 (10)^(2a+2)`: the block after the separator 1 where the tick turns. -/
def T (a : Nat) (L : Tape) : Tape := {lt(T)}
/-- The same after the turn. -/
def T' (a : Nat) (L : Tape) : Tape := {lt(T2)}
/-- `(0101)^b 0 1 0 0 R`, right of the head during the right pass. -/
def A0100 (b : Nat) (R : Tape) : Tape := {rt(A0100)}
/-- What the right pass leaves on the left for a pair. -/
def V (b c : Nat) (L : Tape) : Tape := {lt(V)}
/-- `(10)^(2e+2) 1 0^inf`: the last block and the end of the tape. -/
def R0 (e : Nat) : Tape := {rt(R0)}
/-- The last two blocks after a tick. -/
def Fin (d e : Nat) (L : Tape) : Tape := {lt(FIN)}
/-- `L 1 (10)^(2p+3) 1 (10)^(2a+3)`: two odd blocks after separators 1, where the tick turns. -/
def To (p a : Nat) (L : Tape) : Tape := {lt(TO)}
/-- The same after the turn. -/
def To' (p a : Nat) (L : Tape) : Tape := {lt(TO2)}
/-- `0 1 0 R`. -/
def D010 (R : Tape) : Tape := cons false (cons true (cons false R))
"""


DOC = """# Ticks over chains of even blocks, of any length

In block notation (README), the tick of `x | a . b1 . c1 . … . bk . ck . d . e` with all blocks even, for any number
k of pairs.  The pieces `enter`, `lu`, `turn`, `ru`, `leave` are symbolic runs (`py/chain.py` with
`tools/py/bbtools/symtm.py`; re-bracketings by `py/tapeeq.py`); `left_pass` and `right_pass` are inductions on the
list of pairs, and `tick_chain` is the whole tick: from `⟨Q d e (P ps (T a L)), 1 1 0^inf, A⟩` the machine
reaches `⟨Fin d e (W ps d (T' a L)), 1 1 0^inf, A⟩`, the next right-end turn, for every list `ps`, all a, d, e and
every tape L.  `tick_chain_oo` is the same for `x | p | a . b1 . c1 . … . d . e` with p and a odd (the turn
`turn_oo`).  Block lengths: `(1010)^(n+1)` is an even block of length 2n+2, `10 (1010)^v 1010` an odd one of 2v+3."""

LEAN = """/-- The left pass over a list of pairs: the block it ends on and what it leaves on the right. -/
def LP : List (Nat × Nat) → Nat → Tape → Nat × Tape
  | [], d, R => (d, R)
  | (c, b) :: ps, d, R => LP ps b (U c d R)

/-- What the right pass leaves on the left. -/
def W : List (Nat × Nat) → Nat → Tape → Tape
  | [], _, L => L
  | (c, b) :: ps, _, L => V b c (W ps b L)

theorem left_pass (L : Tape) : ∀ (ps : List (Nat × Nat)) (d : Nat) (R : Tape), ∃ n,
    steps n ⟨Rot d (P ps L), D010 R, .D⟩ = some ⟨Rot (LP ps d R).1 L, D010 (LP ps d R).2, .D⟩ := by
  intro ps
  induction ps with
  | nil => intro d R; exact ⟨0, rfl⟩
  | cons p ps ih =>
    obtain ⟨c, b⟩ := p
    intro d R
    obtain ⟨n, hn⟩ := ih b (U c d R)
    exact ⟨_, steps_seq trans (lu b c d (P ps L) R) hn⟩

theorem right_pass (L : Tape) : ∀ (ps : List (Nat × Nat)) (d : Nat) (R : Tape), ∃ n,
    steps n ⟨L, A0100 (LP ps d R).1 (LP ps d R).2, .A⟩ = some ⟨W ps d L, A0100 d R, .A⟩ := by
  intro ps
  induction ps with
  | nil => intro d R; exact ⟨0, rfl⟩
  | cons p ps ih =>
    obtain ⟨c, b⟩ := p
    intro d R
    obtain ⟨n, hn⟩ := ih b (U c d R)
    exact ⟨_, steps_seq trans hn (ru b c d (W ps b L) R)⟩

/-- A whole tick of `x | a . b1 . c1 . … . bk . ck . d . e` (all blocks even, any k), from one right-end turn to the
next. -/
theorem tick_chain (L : Tape) (a d e : Nat) (ps : List (Nat × Nat)) : ∃ n,
    steps n ⟨Q d e (P ps (T a L)), cons true (cons true blank), .A⟩ =
      some ⟨Fin d e (W ps d (T' a L)), cons true (cons true blank), .A⟩ := by
  obtain ⟨n1, h1⟩ := left_pass (T a L) ps d (R0 e)
  obtain ⟨n2, h2⟩ := right_pass (T' a L) ps d (R0 e)
  exact ⟨_, steps_seq trans (enter d e (P ps (T a L)))
    (steps_seq trans h1 (steps_seq trans (turn a _ L _) (steps_seq trans h2 (leave d e (W ps d (T' a L))))))⟩

/-- A whole tick of `x | p | a . b1 . c1 . … . bk . ck . d . e` with p, a odd and the rest even (any k). -/
theorem tick_chain_oo (L : Tape) (p a d e : Nat) (ps : List (Nat × Nat)) : ∃ n,
    steps n ⟨Q d e (P ps (To p a L)), cons true (cons true blank), .A⟩ =
      some ⟨Fin d e (W ps d (To' p a L)), cons true (cons true blank), .A⟩ := by
  obtain ⟨n1, h1⟩ := left_pass (To p a L) ps d (R0 e)
  obtain ⟨n2, h2⟩ := right_pass (To' p a L) ps d (R0 e)
  exact ⟨_, steps_seq trans (enter d e (P ps (To p a L)))
    (steps_seq trans h1 (steps_seq trans (turn_oo p a _ L _) (steps_seq trans h2 (leave d e (W ps d (To' p a L))))))⟩
"""


def main():
    parts = [defs()]
    parts += rule("enter", f"{Q} A> 1 1 0^inf", f"{ROT} D> 0 1 0 {R0}", ["d", "e"],
                  "⟨Q d e L, cons true (cons true blank), .A⟩", "⟨Rot d L, D010 (R0 e), .D⟩",
                  "A crosses the last block leftwards.")
    parts += rule("lu", f"{PC} 0 1 0 1 (0101)^d D> 0 1 0 R", f"L 0 1 0 1 (0101)^b D> 0 1 0 {U}", ["b", "c", "d"],
                  "⟨Rot d (Pc c b L), D010 R, .D⟩", "⟨Rot b L, D010 (U c d R), .D⟩",
                  "The left pass over one pair of blocks.")
    parts += rule("turn", f"{T} 0 1 0 1 (0101)^b D> 0 1 0 R", f"{T2} A> {A0100}", ["a", "b"],
                  "⟨Rot b (T a L), D010 R, .D⟩", "⟨T' a L, A0100 b R, .A⟩",
                  "The turn at the separator 1.")
    parts += rule("turn_oo", f"{TO} 0 1 0 1 (0101)^b D> 0 1 0 R", f"{TO2} A> {A0100}", ["p", "a", "b"],
                  "⟨Rot b (To p a L), D010 R, .D⟩", "⟨To' p a L, A0100 b R, .A⟩",
                  "The turn at two odd blocks after separators 1.")
    parts += rule("ru", f"L A> (0101)^b 0 1 0 0 {U}", f"{V} A> (0101)^d 0 1 0 0 R", ["b", "c", "d"],
                  "⟨L, A0100 b (U c d R), .A⟩", "⟨V b c L, A0100 d R, .A⟩",
                  "The right pass over one pair of blocks.")
    parts += rule("leave", f"L A> (0101)^d 0 1 0 0 {R0}", f"{FIN} A> 1 1 0^inf", ["d", "e"],
                  "⟨L, A0100 d (R0 e), .A⟩", "⟨Fin d e L, cons true (cons true blank), .A⟩",
                  "The last block, back at the right end.")
    parts.append(LEAN)
    with open(os.path.join(HERE, "..", "lean", "Chain.lean"), "w") as f:
        f.write(rules_file("Machine", NS, parts, DOC))


if __name__ == "__main__":
    main()
