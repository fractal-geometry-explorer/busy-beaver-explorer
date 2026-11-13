import Machine
import Rules

/-!
# 1RB1RF_1LC1LF_---1LD_1LE0RA_1RE1LB_1RD0LD: the marker, restated and iterated

Read as runs of 1s separated by single 0s, the tape is a list of digits, mostly 2s (`110`). `Mk a b R` is the
configuration `0^inf D> 0 0 (110)^a 1110 (110)^b R`: the head in state D at the left end, a block of a digits 2, the
marker 3 (`1110`), a block of b digits 2, the rest R.  Two sweeps (`marker`, from `Rules.lean`) take `Mk a (b+1) R`
to `Mk (a+3) b R` (`marker'`): the marker moves one digit right while the block on its left gains three digits, one
from it and two grown at the end of the tape.  `markers` iterates it j times.
-/

namespace H25899

open TM

/-- `0^inf D> 0 0 (110)^a 1110 (110)^b R`. -/
def Mk (a b : Nat) (R : Tape) : Config :=
  ⟨blank, cons false (cons false (rep a [true, true, false] (cons true (cons true (cons true (cons false
    (rep b [true, true, false] R))))))), .D⟩

theorem rot (a : Nat) (X : Tape) :
    cons true (rep a [true, false, true] X) = rep a [true, true, false] (cons true X) :=
  rep_rotate a [true] [true, false, true] [true, true, false] rfl X

theorem marker' (a b : Nat) (R : Tape) :
    steps (24 * a + 70) (Mk a (b + 1) R) = some (Mk (a + 3) b R) := by
  have h := marker a b R
  simp only [rep_succ, app_cons, app_nil] at h
  rw [rot] at h
  unfold Mk
  simp only [rep_succ, app_cons, app_nil]
  exact h

/-- The steps of j double sweeps from `Mk a`. -/
def markers_steps (a : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => (24 * a + 70) + markers_steps (a + 3) j

theorem markers (j a b : Nat) (R : Tape) :
    steps (markers_steps a j) (Mk a (b + j) R) = some (Mk (a + 3 * j) b R) := by
  induction j generalizing a with
  | zero => rfl
  | succ j ih =>
    have h1 := marker' a (b + j) R
    have h2 := ih (a + 3)
    rw [show a + 3 * (j + 1) = a + 3 + 3 * j by omega]
    rw [show b + (j + 1) = b + j + 1 by omega]
    exact steps_seq trans h1 h2

end H25899
