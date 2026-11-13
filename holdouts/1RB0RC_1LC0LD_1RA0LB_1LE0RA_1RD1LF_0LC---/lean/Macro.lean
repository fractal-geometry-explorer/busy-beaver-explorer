import Rules
set_option linter.unusedSimpArgs false

/-!
# The moving particle Q: one bounce, and its travel across a run of `10`s

The head bounces between the left end of the tape and a particle `Q` sitting in a background of `10`s.
At the left end, in state A, the tape is

    Q0 a c R  =  1 A>1 0 (10)^a 0 (10)^c R          (Q in its short form, a single extra 0)
    Q1 a c R  =  1 A>1 0 (10)^a 1 1 0 (10)^c R      (Q in its long form, an extra 1)

(blank tape left of the first 1).  One bounce goes right to Q, comes back, and moves Q one `10` to the right
while the tape grows by two cells at the left:

* `bounce0`: `Q0 a (c+2) R → Q1 (a+2) c R` in `4a + 14` steps;
* `bounce1`: `Q1 a (c+1) R → Q0 (a+2) (c+1) R` in `4a + 10` steps;
* `travel`: k double bounces, `Q0 a (c+1+2k) R → Q0 (a+4k) (c+1) R` in `8ak + 16k² + 16k` steps.

The bounces never look at `R`: everything to the right of Q is untouched while Q travels.
Everything is checked by Lean's kernel.
-/

namespace H54407

open TM

/-- Q in its short form, `a` background pairs on its left and `c` on its right. -/
def Q0 (a c : Nat) (R : Tape) : Config :=
  ⟨cons true blank, cons true (cons false (rep a [true, false] (cons false (rep c [true, false] R)))), .A⟩

/-- Q in its long form. -/
def Q1 (a c : Nat) (R : Tape) : Config :=
  ⟨cons true blank, cons true (cons false (rep a [true, false] (cons true (cons true (cons false
    (rep c [true, false] R)))))), .A⟩

theorem rot1 (a : Nat) (s : Tape) : cons true (rep a [false, true] s) = rep a [true, false] (cons true s) :=
  rep_rotate a [true] [false, true] [true, false] rfl s

theorem push10 (a : Nat) (s : Tape) :
    cons true (cons false (rep a [true, false] s)) = rep a [true, false] (cons true (cons false s)) := by
  rw [show cons true (cons false (rep a [true, false] s)) = rep (a + 1) [true, false] s from rfl,
    ← rep_app_comm]; rfl

theorem bounce0 (a c : Nat) (R : Tape) : steps (4 * a + 14) (Q0 a (c + 2) R) = some (Q1 (a + 2) c R) := by
  have h := bounce0_cells a c R
  rw [rot1, show rep (c + 1) [true, false] R = cons true (cons false (rep c [true, false] R)) from rfl] at h
  simp only [Q0, Q1]
  rw [show rep (a + 2) [true, false] (cons true (cons true (cons false (rep c [true, false] R)))) =
      cons true (cons false (cons true (cons false (rep a [true, false]
        (cons true (cons true (cons false (rep c [true, false] R)))))))) from rfl]
  rw [← push10] at h
  exact h

theorem bounce1 (a c : Nat) (R : Tape) :
    steps (4 * a + 10) (Q1 a (c + 1) R) = some (Q0 (a + 2) (c + 1) R) := by
  have h := bounce1_cells a c R
  rw [rot1] at h
  simp only [Q0, Q1]
  rw [show rep (a + 2) [true, false] (cons false (rep (c + 1) [true, false] R)) =
      cons true (cons false (cons true (cons false (rep a [true, false]
        (cons false (rep (c + 1) [true, false] R)))))) from rfl]
  rw [← push10] at h
  exact h

/-- Two bounces: Q moves one `10` to the right and is back in its short form. -/
theorem bounce2 (a c : Nat) (R : Tape) :
    steps (8 * a + 32) (Q0 a (c + 3) R) = some (Q0 (a + 4) (c + 1) R) := by
  have h1 := bounce0 a (c + 1) R
  have h2 := bounce1 (a + 2) c R
  rw [show a + 2 + 2 = a + 4 by omega] at h2
  exact steps_congr trans (by omega) (steps_seq trans h1 h2)

/-- The cost of k double bounces from `a`. -/
def tcost : Nat → Nat → Nat
  | _, 0 => 0
  | a, k + 1 => 8 * a + 32 + tcost (a + 4) k

theorem tcost_eq (a k : Nat) : tcost a k = 8 * a * k + 16 * (k * k) + 16 * k := by
  induction k generalizing a with
  | zero => simp [tcost]
  | succ k ih =>
    simp only [tcost, ih]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    simp only [Nat.mul_comm, Nat.mul_left_comm]
    omega

/-- **Travel**: k double bounces carry Q across 2k pairs... one pair per double bounce, `c + 1 + 2k` to `c + 1`
on its right, `a` to `a + 4k` on its left. -/
theorem travel (k a c : Nat) (R : Tape) :
    steps (8 * a * k + 16 * (k * k) + 16 * k) (Q0 a (c + 1 + 2 * k) R) = some (Q0 (a + 4 * k) (c + 1) R) := by
  rw [← tcost_eq]
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    have h1 := bounce2 a (c + 2 * k) R
    have h2 := ih (a + 4)
    rw [show c + 2 * k + 3 = c + 1 + 2 * (k + 1) by omega] at h1
    rw [show c + 2 * k + 1 = c + 1 + 2 * k by omega] at h1
    rw [show a + 4 + 4 * k = a + 4 * (k + 1) by omega] at h2
    exact steps_seq trans h1 h2

end H54407
