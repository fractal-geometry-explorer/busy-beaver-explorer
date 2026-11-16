import VisitL

/-! # The base-3 counter of 1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0RE---

Read the cells left of the counter's low end in tokens of three cells, nearest cell first:
`d0 = 010`, `d1 = 110`, `d2 = 100` (digit values 0, 1, 2, lowest digit nearest the head).  A visit in state A adds
one: trailing 2s become 0s, the first digit that is not 2 goes up by one, and the visit comes out in state B if
there was no carry, in E if there was.  A carry through every digit turns the blank cells beyond into a new digit 2.
For every number of digits, from the rows of `VisitL.lean`. -/

namespace H43701

open TM

def d0 : List Bool := [false, true, false]
def d1 : List Bool := [true, true, false]
def d2 : List Bool := [true, false, false]

/-- A carry through k + 1 digits 2, given what the visit of the rest does (it must come out in B or E). -/
theorem n_carry (k : Nat) {x x' : Tape} {r : St} (hr : r = .B ∨ r = .E) (h : VisL .A x r x') :
    VisL .A (rep (k + 1) d2 x) .E (rep (k + 1) d0 x') := by
  induction k with
  | zero =>
    rcases hr with rfl | rfl
    · exact w_A_100_Ab h
    · exact w_A_100_Ae h
  | succ k ih => exact w_A_100_Ae ih

/-- Lowest digit 0: it becomes 1, out in B. -/
theorem n_inc0 (y : Tape) : VisL .A (app d0 y) .B (app d1 y) := w_A_010_none

/-- Lowest digit 1: it becomes 2, out in B. -/
theorem n_inc1 (y : Tape) : VisL .A (app d1 y) .B (app d2 y) := w_A_110_none

/-- k + 1 digits 2, then a 0: the 2s become 0s and the 0 becomes 1, out in E. -/
theorem n_inc0_carry (k : Nat) (y : Tape) :
    VisL .A (rep (k + 1) d2 (app d0 y)) .E (rep (k + 1) d0 (app d1 y)) :=
  n_carry k (Or.inl rfl) (n_inc0 y)

/-- k + 1 digits 2, then a 1: the 2s become 0s and the 1 becomes 2, out in E. -/
theorem n_inc1_carry (k : Nat) (y : Tape) :
    VisL .A (rep (k + 1) d2 (app d1 y)) .E (rep (k + 1) d0 (app d2 y)) :=
  n_carry k (Or.inl rfl) (n_inc1 y)

/-- Blank tape beyond the digits becomes a digit 2. -/
theorem n_new : VisL .A blank .B (app d2 blank) := by
  have h := @w_A_000_none blank
  simp only [cons_false_blank] at h
  rw [show app d2 blank = cons true blank by simp [d2, cons_false_blank]]
  exact h

/-- All k + 1 digits are 2: they become 0s and a new digit 2 appears beyond them, out in E. -/
theorem n_overflow (k : Nat) : VisL .A (rep (k + 1) d2 blank) .E (rep (k + 1) d0 (app d2 blank)) :=
  n_carry k (Or.inl rfl) n_new

end H43701
