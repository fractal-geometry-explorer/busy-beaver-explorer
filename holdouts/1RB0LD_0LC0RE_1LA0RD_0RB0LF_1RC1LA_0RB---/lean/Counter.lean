import VisitR

/-! # The base-3 counter of 1RB0LD_0LC0RE_1LA0RD_0RB0LF_1RC1LA_0RB---

Read the cells right of the counter's low end in tokens of three cells, nearest cell first:
`d0 = 010`, `d1 = 110`, `d2 = 100` (digit values 0, 1, 2, lowest digit nearest the head).  A visit in state C adds
one: trailing 2s become 0s, the first digit that is not 2 goes up by one, and the visit comes out in state A if
there was no carry, in D if there was.  A carry through every digit turns the blank cells beyond into a new digit 2.
For every number of digits, from the rows of `VisitR.lean`. -/

namespace H55410

open TM

def d0 : List Bool := [false, true, false]
def d1 : List Bool := [true, true, false]
def d2 : List Bool := [true, false, false]

/-- A carry through k + 1 digits 2, given what the visit of the rest does (it must come out in A or D). -/
theorem n_carry (k : Nat) {x x' : Tape} {r : St} (hr : r = .A ∨ r = .D) (h : Vis .C x r x') :
    Vis .C (rep (k + 1) d2 x) .D (rep (k + 1) d0 x') := by
  induction k with
  | zero =>
    rcases hr with rfl | rfl
    · exact v_C_100_Ca h
    · exact v_C_100_Cd h
  | succ k ih => exact v_C_100_Cd ih

/-- Lowest digit 0: it becomes 1, out in A. -/
theorem n_inc0 (y : Tape) : Vis .C (app d0 y) .A (app d1 y) := v_C_010_none

/-- Lowest digit 1: it becomes 2, out in A. -/
theorem n_inc1 (y : Tape) : Vis .C (app d1 y) .A (app d2 y) := v_C_110_none

/-- k + 1 digits 2, then a 0: the 2s become 0s and the 0 becomes 1, out in D. -/
theorem n_inc0_carry (k : Nat) (y : Tape) :
    Vis .C (rep (k + 1) d2 (app d0 y)) .D (rep (k + 1) d0 (app d1 y)) :=
  n_carry k (Or.inl rfl) (n_inc0 y)

/-- k + 1 digits 2, then a 1: the 2s become 0s and the 1 becomes 2, out in D. -/
theorem n_inc1_carry (k : Nat) (y : Tape) :
    Vis .C (rep (k + 1) d2 (app d1 y)) .D (rep (k + 1) d0 (app d2 y)) :=
  n_carry k (Or.inl rfl) (n_inc1 y)

/-- Blank tape beyond the digits becomes a digit 2. -/
theorem n_new : Vis .C blank .A (app d2 blank) := by
  have h := @v_C_000_none blank
  simp only [cons_false_blank] at h
  rw [show app d2 blank = cons true blank by simp [d2, cons_false_blank]]
  exact h

/-- All k + 1 digits are 2: they become 0s and a new digit 2 appears beyond them, out in D. -/
theorem n_overflow (k : Nat) : Vis .C (rep (k + 1) d2 blank) .D (rep (k + 1) d0 (app d2 blank)) :=
  n_carry k (Or.inl rfl) n_new

end H55410
