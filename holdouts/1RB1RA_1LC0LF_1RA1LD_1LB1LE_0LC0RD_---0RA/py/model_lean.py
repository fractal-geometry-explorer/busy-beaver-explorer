"""Writes lean/Model.lean: the tape moves behind the stack model of py/model.py, each for any surrounding tape.

The moves with a repeat count are proved by `bbtools.symtm.prove`, the others are single runs of a few steps.
usage: python3 model_lean.py > ../lean/Model.lean
"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "tools", "py"))
from bbtools.symtm import prove

M = "1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA"

HEAD = '''import Machine

/-! # The tape moves behind the stack model

Written by `py/model_lean.py`.  `py/model.py` describes the run as a stack of frames `1^n 0^z` with, on top, one of
`RET(q, v)`: `1^(q-1) C>1 :: v`, `Z(v)`: C on the last zero of the top frame, `CALL(m, X)`: `1^m B> X`, where the
words are over b = 110 and c = 111.  Every transition of that model is one of the moves below (`Z` is `z_turn`
followed by `a_run`), and each move is proved here for any tape `L`, `R` around it.  The model itself (which move applies when,
and the bookkeeping of the frames) is checked against direct simulation, not in Lean. -/

namespace H129887

open TM

/-- A returns to the right over a run of 1s and turns the 0 behind it into a 1: `L A> 1^n 0 R` reaches
`L 1^n 1 B> R`.  (After `Z`.) -/
'''

FIXED = '''
/-- One stride of the returning head: `L y 1 1 C>1 R` reaches `L C>y 0 1 1 R`: the head moves three cells to the
left and leaves a token `b` (in the phase `0 1 1`) behind.  `RET(q, v)` becomes `RET(q - 3, b v)`. -/
theorem stride1 (y : Bool) (L R : Tape) :
    steps 5 ⟨cons true (cons true (cons y L)), cons true R, .C⟩
      = some ⟨L, cons y (cons false (cons true (cons true R))), .C⟩ := by
  cases y <;> rfl

/-- The stride of `RET(2, v)`: the third cell is the frame's last zero: `L y 0 1 C>1 R` reaches `L C>y 0 1 1 R`. -/
theorem stride_q2 (y : Bool) (L R : Tape) :
    steps 3 ⟨cons true (cons false (cons y L)), cons true R, .C⟩
      = some ⟨L, cons y (cons false (cons true (cons true R))), .C⟩ := by
  cases y <;> rfl

/-- `RET(1, v)` on a frame with at least two zeros: `L y 0 0 C>1 R` reaches `L C>y 1 1 1 R`: two zeros are filled,
the word gets a `c` in front.  With `y = 0` this is `Z(c v)`, with `y = 1` (the frame had two zeros) the head is on
the last 1 of the frame below: `RET(n, c v)`. -/
theorem ret1_fill (y : Bool) (L R : Tape) :
    steps 3 ⟨cons false (cons false (cons y L)), cons true R, .C⟩
      = some ⟨L, cons y (cons true (cons true (cons true R))), .C⟩ := by
  cases y <;> rfl

/-- `RET(1, v)` on a frame with one zero and at least two 1s below it: `L 1 1 0 C>1 R` reaches `L 0 1 B>1 1 R`,
which is `CALL(1, v)` on a frame with one zero. -/
theorem ret1_split (L R : Tape) :
    steps 5 ⟨cons false (cons true (cons true L)), cons true R, .C⟩
      = some ⟨cons true (cons false L), cons true (cons true R), .B⟩ := rfl

/-- **The halting pattern.**  `RET(1, v)` on a frame `1 0` (one 1, one zero) above a zero: `L 0 1 0 C>1 R` halts
on its fourth step (three transitions, then F reads 0). -/
theorem halt_pattern (L R : Tape) :
    ∃ c, steps 3 ⟨cons false (cons true (cons false L)), cons true R, .C⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- `Z(v)`: C on a zero turns right: `L C>0 R` reaches `L 1 A> R`. -/
theorem z_turn (L R : Tape) : steps 1 ⟨L, cons false R, .C⟩ = some ⟨cons true L, R, .A⟩ := rfl
'''

GEN = [
    ("a_run", "L A> 1^n 0 R", "L 1^n 1 B> R", None),
    ("b_eat", "L 1 B> 1^n R", "L 0^n 1 B> R",
     "B eats a run of 1s, carrying one 1 along: `L 1 B> 1^n R` reaches `L 0^n 1 B> R`."),
    ("stride", "L (111)^n C> 1 R", "L C> 1 (011)^n R",
     "`n` strides in a row: `L (111)^n C>1 R` reaches `L C>1 (011)^n R`.  `RET(q + 3 n, v)` becomes `RET(q, b^n v)`."),
    ("call_cb", "L 1 B> (111)^j 110 R", "L 00 (000)^j C> 11 R",
     "`CALL(m, c^j b Y)`: `L 1 B> (111)^j 110 R` reaches `L 0^(3j+2) C>1 1 R`: the `1` behind the head, the block "
     "of c's and the b are now `3 j + 2` zeros (the new frame) and `RET(1, c Y)`."),
    ("call_c", "L 1 B> (111)^j 0 R", "L (000)^j C> 11 R",
     "`CALL(m, c^j)` at the end of the word: `L 1 B> (111)^j 0 R` reaches `L 0^(3j) C>1 1 R`, which is `RET(1, c)` "
     "on a frame with `3 j` zeros (`j = 0`: `RET(m, c)`)."),
]


def main():
    out = [HEAD.rstrip("\n")]
    first = True
    for name, a, b, doc in GEN:
        t, _ = prove(M, name, a, b, doc=doc)
        out.append(t.rstrip("\n") + "\n")
    out.append(FIXED.strip("\n"))
    out.append("\nend H129887")
    print("\n".join(out))


main()
