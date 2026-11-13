import Machine
import Rules

/-!
# The transfer cycle of 1RB0RA_1LC0RD_0LD0LB_1RA0LE_1LF---_0RA1LB

`cyc x R` is the configuration with the head (state C) on the left end of the tape, the gadget
`0 1 0 1 0 111 0 1 00 1 0 11 0`, then `(10)^(2x)`, the marker `111 0`, and the rest `R` of the tape.
`cycle`: one transfer cycle moves the marker 12 pairs left and leaves 15 pairs `10` behind it.
`cycles`: k cycles at once.
-/

namespace H65987

open TM

/-- The gadget at the left end. -/
def gad (T : Tape) : Tape :=
  app [false, true, false, true, false, true, true, true, false, true, false, false, true, false, true, true, false] T

/-- Gadget, `(10)^(2x)`, marker `111 0`, rest `R`; head C on the first cell, blank tape to the left. -/
def cyc (x : Nat) (R : Tape) : Config :=
  ⟨blank, gad (rep x [true, false, true, false] (app [true, true, true, false] R)), .C⟩

theorem rep15 (R : Tape) : rep 15 [true, false] R = (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false R)))))))))))))))))))))))))))))) := rfl

/-- One cycle: `G (10)^(2x+12) 111 0 R` reaches `G (10)^(2x) 111 0 (10)^15 R` in 120x + 878 steps. -/
theorem cycle (x : Nat) (R : Tape) : steps (120 * x + 878) (cyc (x + 6) R) = some (cyc x (rep 15 [true, false] R)) := by
  have h := cycle_cells x R
  have r := rep_rotate x [true] [false, true, false, true] [true, false, true, false] rfl
    (cons true (cons true (cons false (rep 15 [true, false] R))))
  simp only [app] at r
  simp only [cyc, gad, app]
  rw [← r, rep15]
  exact h

/-- The cost of k cycles ending at `x`: the sum of 120 (x + 6i) + 878 for i < k, which is
k (120 x + 878) + 360 k (k - 1). -/
def ccost (x : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => ccost (x + 6) k + (120 * x + 878)

/-- k cycles at once: `G (10)^(2x+12k) 111 0 R` reaches `G (10)^(2x) 111 0 (10)^(15k) R`. -/
theorem cycles (k : Nat) : ∀ x R, steps (ccost x k) (cyc (x + 6 * k) R) = some (cyc x (rep (15 * k) [true, false] R)) := by
  induction k with
  | zero => intro x R; rfl
  | succ k ih =>
    intro x R
    have h1 := ih (x + 6) R
    have h2 := cycle x (rep (15 * k) [true, false] R)
    have e : x + 6 + 6 * k = x + 6 * (k + 1) := by omega
    rw [e] at h1
    have e2 : rep 15 [true, false] (rep (15 * k) [true, false] R) = rep (15 * (k + 1)) [true, false] R := by
      rw [← rep_add]; congr 1; omega
    rw [e2] at h2
    exact steps_seq trans h1 h2

end H65987
