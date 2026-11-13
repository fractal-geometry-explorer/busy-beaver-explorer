import Rules

/-!
# 1RB1LC_1LA0RE_0LD---_1RE0LF_1RF0RD_1LD0LB: rounds at the left end, by induction

`cfg x j y R` is `0^inf D> 0 (10)^x j (10)^y R`.  A half-round (`half_round_0`, `half_round_1` of
`Rules.lean`) moves one word 10 from the right block to the left block, adds one more, and flips the junction cell j;
`rounds` chains k full rounds.  None of them reads R.
-/

namespace H166700

open TM

/-- `0^inf D> 0 (10)^x j (10)^y R` -/
def cfg (x : Nat) (j : Bool) (y : Nat) (R : Tape) : Config :=
  ⟨blank, cons false (rep x [true, false] (cons j (rep y [true, false] R))), .D⟩

theorem rot (x : Nat) (s : Tape) :
    cons true (rep x [false, true] s) = rep x [true, false] (cons true s) := by
  have h := rep_rotate x [true] [false, true] [true, false] rfl s
  simpa [app] using h

theorem two (x : Nat) (s : Tape) :
    rep (x + 2) [true, false] s = app [true, false] (rep x [true, false] (app [true, false] s)) := by
  rw [rep_app_comm]; rfl

theorem half0 (x y : Nat) (R : Tape) : steps (4 * x + 10) (cfg x false (y + 1) R) = some (cfg (x + 2) true y R) := by
  have h := half_round_0 x y R
  rw [rot] at h
  simp only [cfg, two]
  exact h

theorem half1 (x y : Nat) (R : Tape) : steps (4 * x + 6) (cfg x true (y + 1) R) = some (cfg (x + 2) false y R) := by
  have h := half_round_1 x y R
  rw [rot] at h
  simp only [cfg, two]
  exact h

/-- k full rounds: (x, 0, y + 2k) -> (x + 4k, 0, y). -/
theorem rounds (k : Nat) : ∀ x y R, ∃ n, steps n (cfg x false (y + 2 * k) R) = some (cfg (x + 4 * k) false y R) := by
  induction k with
  | zero => intro x y R; exact ⟨0, rfl⟩
  | succ k ih =>
    intro x y R
    obtain ⟨n, hn⟩ := ih (x + 4) y R
    have e1 : y + 2 * (k + 1) = (y + 2 * k + 1) + 1 := by omega
    have e2 : x + 4 + 4 * k = x + 4 * (k + 1) := by omega
    rw [e2] at hn
    rw [e1]
    exact ⟨_, steps_seq trans (half0 x _ R) (steps_seq trans (half1 (x + 2) _ R) hn)⟩

end H166700
