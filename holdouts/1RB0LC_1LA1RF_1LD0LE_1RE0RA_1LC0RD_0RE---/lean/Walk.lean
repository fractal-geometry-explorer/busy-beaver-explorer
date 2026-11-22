import WalkRules
set_option linter.unusedSimpArgs false

/-!
# The reflector Q: one bounce, and its walk across a run of pairs

When the last run of pairs is used up, the head stops crossing the whole tape.  It bounces between the right end
of the tape (blank beyond it) and a reflector `Q`, a single extra cell in a background of pairs `01`.  At the right
end, in state E, the tape is

    Q0 c a L  =  L (01)^c 0 (01)^a E>        (Q in its short form, an extra 0)
    Q1 c a L  =  L (01)^c 1 (01)^a E>        (Q in its long form, an extra 1)

(blank tape right of the head).  One bounce goes left to Q, comes back, and moves Q two cells to the left, one pair
of the background on its left now on its right, while the tape grows by two cells at the right end:

* `bounce0`: `Q0 (c+1) (a+1) L → Q1 c (a+3) L` in `4a + 14` steps;
* `bounce1`: `Q1 (c+1) (a+1) L → Q0 c (a+3) L` in `4a + 10` steps;
* `walk`: k double bounces, `Q0 (c+2k) (a+1) L → Q0 c (a+1+4k) L` in `8ak + 16k² + 16k` steps.

The bounces never look at `L`: everything left of the pairs Q is crossing is untouched.  This is the mirror image
of the travelling particle of `1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RD1LF_0LC---` (the same table, renamed and mirrored).
Everything is checked by Lean's kernel.
-/

namespace H71372

open TM

/-- Q in its short form: `c` background pairs on its left, `a` on its right, then the right end. -/
def Q0 (c a : Nat) (L : Tape) : Config :=
  ⟨rep a [true, false] (cons false (rep c [true, false] L)), blank, .E⟩

/-- Q in its long form. -/
def Q1 (c a : Nat) (L : Tape) : Config :=
  ⟨rep a [true, false] (cons true (rep c [true, false] L)), blank, .E⟩

theorem rot1 (a : Nat) (s : Tape) : cons true (rep a [false, true] s) = rep a [true, false] (cons true s) :=
  rep_rotate a [true] [false, true] [true, false] rfl s

theorem push10 (a : Nat) (s : Tape) :
    cons true (cons false (rep a [true, false] s)) = rep a [true, false] (cons true (cons false s)) := by
  rw [show cons true (cons false (rep a [true, false] s)) = rep (a + 1) [true, false] s from rfl,
    ← rep_app_comm]; rfl

/-- The run's way of writing the tape after a bounce is the next form of Q. -/
theorem rebracket (a : Nat) (x : Bool) (S : Tape) :
    cons true (cons false (cons true (rep a [false, true] (cons false (cons true (cons false (cons x S)))))))
      = rep (a + 3) [true, false] (cons x S) := by
  rw [rot1, push10, rep_add a 3]; rfl

theorem bounce0 (c a : Nat) (L : Tape) : steps (4 * a + 14) (Q0 (c + 1) (a + 1) L) = some (Q1 c (a + 3) L) := by
  have h := bounce0_cells a c L
  rw [rebracket a true] at h
  exact h

theorem bounce1 (c a : Nat) (L : Tape) : steps (4 * a + 10) (Q1 (c + 1) (a + 1) L) = some (Q0 c (a + 3) L) := by
  have h := bounce1_cells a c L
  rw [rebracket a false] at h
  exact h

/-- Two bounces: Q moves four cells (two pairs) to the left and is back in its short form; the right end has grown
by four cells. -/
theorem bounce2 (c a : Nat) (L : Tape) :
    steps (8 * a + 32) (Q0 (c + 2) (a + 1) L) = some (Q0 c (a + 5) L) := by
  have h1 := bounce0 (c + 1) a L
  have h2 := bounce1 c (a + 2) L
  rw [show a + 2 + 1 = a + 3 by omega, show a + 2 + 3 = a + 5 by omega] at h2
  exact steps_congr trans (by omega) (steps_seq trans h1 h2)

/-- The cost of k double bounces from `a + 1` pairs on the right of Q. -/
def wcost : Nat → Nat → Nat
  | _, 0 => 0
  | a, k + 1 => 8 * a + 32 + wcost (a + 4) k

theorem wcost_eq (a k : Nat) : wcost a k = 8 * a * k + 16 * (k * k) + 16 * k := by
  induction k generalizing a with
  | zero => simp [wcost]
  | succ k ih =>
    simp only [wcost, ih]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    simp only [Nat.mul_comm, Nat.mul_left_comm]
    omega

/-- **Walk**: k double bounces carry Q across 2k pairs to the left: `c + 2k` pairs on its left become `c`, and
`a + 1` on its right become `a + 1 + 4k` (the 2k pairs it crossed and 2k new ones at the right end). -/
theorem walk (k c a : Nat) (L : Tape) :
    steps (8 * a * k + 16 * (k * k) + 16 * k) (Q0 (c + 2 * k) (a + 1) L) = some (Q0 c (a + 1 + 4 * k) L) := by
  rw [← wcost_eq]
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    have h1 := bounce2 (c + 2 * k) a L
    have h2 := ih (a + 4)
    rw [show c + 2 * k + 2 = c + 2 * (k + 1) by omega] at h1
    rw [show a + 4 + 1 = a + 5 by omega, show a + 4 + 1 + 4 * k = a + 1 + 4 * (k + 1) by omega] at h2
    exact steps_seq trans h1 h2

end H71372
