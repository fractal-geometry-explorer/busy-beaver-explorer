import Machine
import Rules

/-!
# The phase of 1RB0RA_1LC1RA_0LD1LD_0LE0LC_1LA0LF_---1LC

`P x y w R` is `A>0 (10)^x 00 (10)^y 110 0 1^w 0 R` with the head (state A) on the left end of the tape and blank
tape to its left.  `cycle`: one cycle gives `P (x+3) y (w+2) R` from `P x (y+1) w R`, in 8x + 4(y+1) + 26 steps,
for every x, y, w and every tape `R`.  `phase`: y cycles at once, `P x y w R` to `P (x+3y) 0 (w+2y) R`.
-/

namespace H154944

open TM

/-- `A>0 (10)^x 00 (10)^y 110 0 1^w 0 R`. -/
def P (x y w : Nat) (R : Tape) : Config :=
  ⟨blank, cons false (rep x [true, false] (cons false (cons false (rep y [true, false]
    (cons true (cons true (cons false (cons false (rep w [true] (cons false R)))))))))), .A⟩

theorem r2 (a : Nat) (s : Tape) : rep (2 * a) [true, false] s = rep a [true, false, true, false] s := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [show 2 * (a + 1) = 2 * a + 1 + 1 by omega, rep_succ, rep_succ, ih]
    rfl

theorem r2' (a : Nat) (s : Tape) :
    rep (2 * a + 1) [true, false] s = rep a [true, false, true, false] (cons true (cons false s)) := by
  rw [rep_add, r2]; rfl

theorem rot (b : Nat) (s : Tape) :
    cons true (rep b [false, true, false, true] s) = rep b [true, false, true, false] (cons true s) :=
  rep_rotate b [true] [false, true, false, true] [true, false, true, false] rfl s

theorem rot2 (b : Nat) (s : Tape) :
    cons true (cons false (rep b [true, false, true, false] s)) =
      rep b [true, false, true, false] (cons true (cons false s)) :=
  rep_rotate b [true, false] [true, false, true, false] [true, false, true, false] rfl s

theorem r3 (n : Nat) (s : Tape) :
    rep (n + 3) [true, false] s = cons true (cons false (cons true (cons false (cons true (cons false
      (rep n [true, false] s)))))) := rfl

theorem w2 (w : Nat) (s : Tape) : rep (w + 2) [true] s = cons true (cons true (rep w [true] s)) := rfl

/-- One cycle. -/
theorem cycle (x y w : Nat) (R : Tape) :
    steps (8 * x + 4 * (y + 1) + 26) (P x (y + 1) w R) = some (P (x + 3) y (w + 2) R) := by
  obtain ⟨a, hx⟩ : ∃ a, x = 2 * a ∨ x = 2 * a + 1 := ⟨x / 2, by omega⟩
  obtain ⟨b, hy⟩ : ∃ b, y = 2 * b ∨ y = 2 * b + 1 := ⟨y / 2, by omega⟩
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · have h := cyc_ee a b w R
    rw [show 8 * (2 * a) + 4 * (2 * b + 1) + 26 = 16 * a + 8 * b + 30 by omega]
    simp only [P, r3, w2, r2, r2']
    rw [rot] at h
    exact h
  · have h := cyc_eo a b w R
    rw [show 8 * (2 * a) + 4 * (2 * b + 1 + 1) + 26 = 16 * a + 8 * b + 34 by omega]
    simp only [P, r3, w2, r2, r2', show 2 * b + 1 + 1 = 2 * (b + 1) by omega]
    rw [rot, rot2 b] at h
    exact h
  · have h := cyc_oe a b w R
    rw [show 8 * (2 * a + 1) + 4 * (2 * b + 1) + 26 = 16 * a + 8 * b + 38 by omega,
      show 2 * a + 1 + 3 = 2 * (a + 2) by omega]
    simp only [P, w2, r2, r2']
    rw [rot] at h
    exact h
  · have h := cyc_oo a b w R
    rw [show 8 * (2 * a + 1) + 4 * (2 * b + 1 + 1) + 26 = 16 * a + 8 * b + 42 by omega,
      show 2 * a + 1 + 3 = 2 * (a + 2) by omega]
    simp only [P, w2, r2, r2', show 2 * b + 1 + 1 = 2 * (b + 1) by omega]
    rw [rot, rot2 b] at h
    exact h

/-- The cost of the y cycles of a phase from `P x y w R`. -/
def pcost (x : Nat) : Nat → Nat
  | 0 => 0
  | y + 1 => (8 * x + 4 * (y + 1) + 26) + pcost (x + 3) y

/-- A whole phase: `P x y w R` reaches `P (x + 3y) 0 (w + 2y) R`. -/
theorem phase (y : Nat) : ∀ x w R, steps (pcost x y) (P x y w R) = some (P (x + 3 * y) 0 (w + 2 * y) R) := by
  induction y with
  | zero => intro x w R; rfl
  | succ y ih =>
    intro x w R
    have h := steps_seq trans (cycle x y w R) (ih (x + 3) (w + 2) R)
    rw [show x + 3 + 3 * y = x + 3 * (y + 1) by omega, show w + 2 + 2 * y = w + 2 * (y + 1) by omega] at h
    exact h

end H154944
