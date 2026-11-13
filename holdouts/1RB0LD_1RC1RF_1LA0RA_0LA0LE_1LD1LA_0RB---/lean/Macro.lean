import Rules
set_option linter.unusedSimpArgs false

/-!
# 1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---: the macro machine on (z, y)

At the left end of the tape, in state A, the tape is

    S x z R  =  A>0 (10)^x 0 10 0^z R

(the head on the leftmost visited cell, blank tape to the left).  The *wall* `C z y = S 0 z (tl y)` is the
configuration with nothing grown yet, `tl y = (10)^y 0 1` then blank tape.

* `sweep`: one sweep of the head eats three 0s of the gap and adds two `10`s on the left:
  `S x (z+3) R -> S (x+2) z R` in `4x + 11` steps; `sweeps`: k of them.
* `end0`, `end1`, `end2`: when fewer than three 0s are left (z = 0, 1, 2), the head erases the grown part, walks
  to the right end and back, and a new wall starts with a gap twice as long as what was grown:
  `S x 0 (tl y) -> C (2x+1) (y+4)`, `S x 1 (tl (y+1)) -> C (2x+5) (y+7)`, `S x 2 (tl (y+1)) -> C (2x+8) y`.
* So, with `z = 3k + r`, one macro step is
  `(3k, y) -> (4k+1, y+4)`, `(3k+1, y) -> (4k+5, y+6)`, `(3k+2, y) -> (4k+8, y-1)` (the last two need y ≥ 1):
  `next`, `next_sound`, with the step count `mcost`.

Everything is checked by Lean's kernel.
-/

namespace H141950

open TM

/-- The right part: `(10)^y 0 1`, then blank tape. -/
def tl (y : Nat) : Tape := rep y [true, false] (cons false (cons true blank))

/-- `A>0 (10)^x 0 10 0^z R`, blank tape to the left of the head. -/
def S (x z : Nat) (R : Tape) : Config :=
  ⟨blank, cons false (rep x [true, false] (cons false (cons true (cons false (rep z [false] R))))), .A⟩

/-- The wall configuration `(z, y)`: `A>0 0 10 0^z (10)^y 0 1`. -/
def C (z y : Nat) : Config := S 0 z (tl y)

theorem rep_ff (n : Nat) (s : Tape) : rep n [false, false] s = rep (2 * n) [false] s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
    show cons false (cons false (rep n [false, false] s)) = cons false (rep (2 * n + 1) [false] s)
    rw [ih]; rfl

theorem rep_comm (y k : Nat) (w : List Bool) (s : Tape) : rep y w (rep k w s) = rep (y + k) w s :=
  (rep_add y k w s).symm

/-- One sweep. -/
theorem sweep (x z : Nat) (R : Tape) : steps (4 * x + 11) (S x (z + 3) R) = some (S (x + 2) z R) := by
  have h := sweep_cells x z R
  have e : rep (x + 2) [true, false] (cons false (cons true (cons false (rep z [false] R)))) =
      cons true (cons false (rep x [true, false] (cons true (cons false (cons false (cons true
        (cons false (rep z [false] R)))))))) := by
    rw [show x + 2 = (x + 1) + 1 from rfl, rep_succ, ← rep_app_comm]; rfl
  simp only [S]; rw [e]; exact h

/-- The cost of k sweeps from `x`. -/
def scost : Nat → Nat → Nat
  | _, 0 => 0
  | x, k + 1 => 4 * x + 11 + scost (x + 2) k

theorem scost_eq (x k : Nat) : scost x k + 4 * k = k * (4 * x + 11) + 4 * (k * k) := by
  induction k generalizing x with
  | zero => simp [scost]
  | succ k ih =>
    have := ih (x + 2)
    simp only [scost]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at this ⊢
    simp only [Nat.mul_comm] at this ⊢
    omega

/-- k sweeps. -/
theorem sweeps (k x z : Nat) (R : Tape) :
    steps (scost x k) (S x (z + 3 * k) R) = some (S (x + 2 * k) z R) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    have h1 := sweep x (z + 3 * k) R
    have h2 := ih (x + 2)
    rw [show z + 3 * k + 3 = z + 3 * (k + 1) by omega] at h1
    rw [show x + 2 + 2 * k = x + 2 * (k + 1) by omega] at h2
    exact steps_seq trans h1 h2

/-! ## The end of a wall: fewer than three 0s left -/

theorem fold0 (n : Nat) (s : Tape) : cons false (rep n [false] s) = rep (n + 1) [false] s := rfl
theorem foldw (n : Nat) (s : Tape) : cons true (cons false (rep n [true, false] s)) = rep (n + 1) [true, false] s :=
  rfl
theorem sfx0 (n : Nat) (s : Tape) : rep n [false] (cons false s) = rep (n + 1) [false] s := rep_app_comm n [false] s
theorem sfxw (n : Nat) (s : Tape) : rep n [true, false] (cons true (cons false s)) = rep (n + 1) [true, false] s :=
  rep_app_comm n [true, false] s

/-- Equal counts give equal tapes. -/
theorem rep_congr {a b : Nat} (h : a = b) (w : List Bool) (s : Tape) : rep a w s = rep b w s := h ▸ rfl

theorem end0 (x y : Nat) : steps (4 * x + 8 * y + 37) (S x 0 (tl y)) = some (C (2 * x + 1) (y + 4)) := by
  cases x with
  | zero =>
    have h := end0z y
    simp only [C, S, tl, rep_zero, rep_ff, fold0, foldw, sfx0, sfxw, rep_comm, Nat.add_assoc] at h ⊢
    exact steps_congr trans (by omega) h
  | succ x =>
    have h := end0s x y
    simp only [C, S, tl, rep_zero, rep_ff, fold0, foldw, sfx0, sfxw, rep_comm, Nat.add_assoc] at h ⊢
    exact steps_congr trans (by omega) h

theorem end1 (x y : Nat) :
    steps (8 * x + 16 * y + 110) (S x 1 (tl (y + 1))) = some (C (2 * x + 5) (y + 7)) := by
  cases x with
  | zero =>
    have h := end1z y
    simp only [C, S, tl, rep_zero, rep_ff, fold0, foldw, sfx0, sfxw, rep_comm, Nat.add_assoc] at h ⊢
    exact steps_congr trans (by omega) h
  | succ x =>
    have h := end1s x y
    simp only [C, S, tl, rep_zero, rep_ff, fold0, foldw, sfx0, sfxw, rep_comm, Nat.add_assoc] at h ⊢
    exact steps_congr trans (by omega) h

theorem end2 (x y : Nat) : steps (8 * x + 28) (S x 2 (tl (y + 1))) = some (C (2 * x + 8) y) := by
  cases x with
  | zero =>
    have h := end2z y
    simp only [C, S, tl, rep_zero, rep_ff, fold0, foldw, sfx0, sfxw, rep_comm, Nat.add_assoc] at h ⊢
    exact steps_congr trans (by omega) h
  | succ x =>
    have h := end2s x y
    simp only [C, S, tl, rep_zero, rep_ff, fold0, foldw, sfx0, sfxw, rep_comm, Nat.add_assoc] at h ⊢
    exact steps_congr trans (by omega) h

end H141950
