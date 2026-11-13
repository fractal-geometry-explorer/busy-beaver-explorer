import Machine
import Rules

/-!
# The sweep configurations and the clean phase

At the start of every sweep of the main regime the tape is

    0^∞ C> 0 1 0 (110)^p 1111 (110)^x 11100 (100)^y R

(`cfg p x y R`): the head in state C on the blank cell at the left end, a *counter* `(110)^p`, the marker `1111`,
and the *front level* `(110)^x 11100 (100)^y` followed by the rest of the tape `R` (the further levels).  One sweep
(`sweep`) turns three `100` into four `110`; a *phase* of `k` sweeps (`phase`) takes `(x, 3k + y)` to `(x + 4k, y)`.
When `y` comes down to 2 or 0 the front level is reset and the next level `(110)^z 11100 (100)^w` ticks
(`reset2`, `reset0`):

    (p, x, 2, z, w + 2)  ->  (p + 2, 0, x + 2, z + 2, w)
    (p, x, 0, z, w + 2)  ->  (p + 2, 0, x,     z + 2, w)

so on a front level that starts empty, `y` follows the Collatz-like map `y ↦ 4y/3` (y ≡ 0 mod 3),
`y ↦ 4(y − 2)/3 + 2` (y ≡ 2 mod 3).  The case y ≡ 1 starts a different regime that is not modelled here.
-/

namespace H112769

open TM

/-- The word `110`. -/
abbrev W : List Bool := [true, true, false]
/-- The word `100`. -/
abbrev V : List Bool := [true, false, false]

/-- A level: `(110)^x 11100 (100)^y` in front of `R`. -/
def lv (x y : Nat) (R : Tape) : Tape :=
  rep x W (cons true (cons true (cons true (cons false (cons false (rep y V R))))))

/-- The sweep configuration `0^∞ C> 0 1 0 (110)^p 1111 T`. -/
def cfg (p : Nat) (T : Tape) : Config :=
  ⟨blank, cons false (cons true (cons false (rep p W (cons true (cons true (cons true (cons true T))))))), .C⟩

theorem rot (n : Nat) (s : Tape) :
    cons true (cons true (rep n [false, true, true] s)) = rep n W (cons true (cons true s)) :=
  rep_rotate n [true, true] [false, true, true] W rfl s

theorem rep_add3 (n : Nat) (w : List Bool) (s : Tape) : rep n w (app w (app w (app w s))) = rep (n + 3) w s := by
  rw [rep_app_comm, rep_app_comm, rep_app_comm]

/-- One sweep, for every counter `p` and front block `x`: three `100` become four `110`. -/
theorem sweep (p x y : Nat) (R : Tape) :
    steps (8 * p + 24 * x + 75) (cfg p (lv x (y + 3) R)) = some (cfg p (lv (x + 4) y R)) := by
  match x with
  | 0 =>
    have h := sweep0 p y R
    rw [rot p] at h
    simpa [cfg, lv] using h
  | 1 =>
    have h := sweep1 p y R
    rw [rot p] at h
    simpa [cfg, lv] using h
  | x + 2 =>
    have h := sweep2 p x y R
    rw [rot (x + 1), rot p] at h
    have e : rep (x + 2 + 4) W (cons true (cons true (cons true (cons false (cons false (rep y V R)))))) =
        app W (app W (rep (x + 1) W (app W (app W (app W (cons true (cons true (cons true (cons false
          (cons false (rep y V R))))))))))) := by
      rw [rep_add3]; rfl
    simp only [cfg, lv, e]
    rw [show 8 * p + 24 * (x + 2) + 75 = 8 * p + 24 * x + 123 by omega]
    exact h


/-- Steps of a phase of `k` sweeps from front block `x`. -/
def pst (p x : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (8 * p + 24 * x + 75) + pst p (x + 4) k

/-- A phase: `k` sweeps take `(x, 3k + y)` to `(x + 4k, y)`. -/
theorem phase (p x k y : Nat) (R : Tape) :
    steps (pst p x k) (cfg p (lv x (3 * k + y) R)) = some (cfg p (lv (x + 4 * k) y R)) := by
  induction k generalizing x with
  | zero => simp [pst]
  | succ k ih =>
    have h1 := sweep p x (3 * k + y) R
    rw [show 3 * k + y + 3 = 3 * (k + 1) + y by omega] at h1
    have h2 := ih (x + 4)
    rw [show x + 4 + 4 * k = x + 4 * (k + 1) by omega] at h2
    exact steps_seq trans h1 h2

theorem rep_wrap (n : Nat) (w : List Bool) (s : Tape) : rep (n + 2) w s = app w (rep n w (app w s)) := by
  rw [rep_app_comm]; rfl

theorem rep_wrap2 (n : Nat) (w : List Bool) (s : Tape) :
    rep (n + 4) w s = app w (rep (n + 1) w (app w (app w s))) := by
  rw [rep_app_comm, rep_app_comm]; rfl

theorem rep_split3 (n : Nat) (w : List Bool) (s : Tape) :
    rep (n + 4) w s = rep (n + 1) w (app w (app w (app w s))) :=
  (rep_add3 (n + 1) w s).symm

theorem rep_split1 (n : Nat) (w : List Bool) (s : Tape) :
    rep (n + 2) w s = rep (n + 1) w (app w s) :=
  (rep_app_comm (n + 1) w s).symm

/-- Phase end with two `100` left (`reset2` of `Rules.lean`, rebracketed): the front level is reset, the counter
gains 2 and the next level ticks. -/
theorem end2 (p x z w : Nat) (R : Tape) :
    steps (16 * p + 32 * x + 16 * z + 262) (cfg p (lv (x + 2) 2 (lv (z + 2) (w + 2) R))) =
      some (cfg (p + 2) (lv 0 (x + 4) (lv (z + 4) w R))) := by
  have h := reset2 p w x z R
  rw [rot (z + 1), rot p] at h
  simp only [cfg, lv]
  rw [rep_wrap p, rep_split3 x, rep_wrap2 z]
  exact h

/-- Phase end with no `100` left (`reset0` of `Rules.lean`, rebracketed). -/
theorem end0 (p x z w : Nat) (R : Tape) :
    steps (16 * p + 16 * x + 16 * z + 158) (cfg p (lv (x + 2) 0 (lv (z + 2) (w + 2) R))) =
      some (cfg (p + 2) (lv 0 (x + 2) (lv (z + 4) w R))) := by
  have h := reset0 p w x z R
  rw [rot (z + 1), rot p] at h
  simp only [cfg, lv]
  rw [rep_split1 x V, rep_wrap2 z]
  exact h

/-- A clean phase on an empty front block with `y ≡ 0 (mod 3)`: `(p, y) ↦ (p + 2, 4y/3)`, the next level ticks. -/
theorem cleanA (p k z w : Nat) (R : Tape) :
    steps (pst p 0 (k + 1) + (16 * p + 16 * (4 * k + 2) + 16 * z + 158))
      (cfg p (lv 0 (3 * (k + 1)) (lv (z + 2) (w + 2) R))) =
      some (cfg (p + 2) (lv 0 (4 * (k + 1)) (lv (z + 4) w R))) := by
  have h1 := phase p 0 (k + 1) 0 (lv (z + 2) (w + 2) R)
  rw [show 0 + 4 * (k + 1) = 4 * k + 2 + 2 by omega, show 3 * (k + 1) + 0 = 3 * (k + 1) by omega] at h1
  have h2 := end0 p (4 * k + 2) z w R
  rw [show 4 * k + 2 + 2 = 4 * (k + 1) by omega] at h2 h1
  exact steps_seq trans h1 h2

/-- A clean phase on an empty front block with `y ≡ 2 (mod 3)`: `(p, y) ↦ (p + 2, 4(y − 2)/3 + 2)`. -/
theorem cleanB (p k z w : Nat) (R : Tape) :
    steps (pst p 0 (k + 1) + (16 * p + 32 * (4 * k + 2) + 16 * z + 262))
      (cfg p (lv 0 (3 * (k + 1) + 2) (lv (z + 2) (w + 2) R))) =
      some (cfg (p + 2) (lv 0 (4 * (k + 1) + 2) (lv (z + 4) w R))) := by
  have h1 := phase p 0 (k + 1) 2 (lv (z + 2) (w + 2) R)
  rw [show 0 + 4 * (k + 1) = 4 * k + 2 + 2 by omega] at h1
  have h2 := end2 p (4 * k + 2) z w R
  rw [show 4 * k + 2 + 4 = 4 * (k + 1) + 2 by omega] at h2
  exact steps_seq trans h1 h2

end H112769
