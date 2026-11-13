import Rules

/-!
# 1RB1LC_1LC0RF_0LF1LD_0LE---_1RF1LC_1LE0RA: the rounds of a phase, by induction

`cfg x y R` is `0^inf F> 0 0 (110)^x 1^y R`.  One round (`round` of `Rules.lean`) adds two words 110 and takes
four ones; `rounds` chains k of them.
-/

namespace H126128

open TM

/-- `0^inf F> 0 0 (110)^x 1^y R` -/
def cfg (x y : Nat) (R : Tape) : Config :=
  ⟨blank, cons false (cons false (rep x [true, true, false] (rep y [true] R))), .F⟩

theorem rot (x : Nat) (s : Tape) :
    cons true (rep x [true, false, true] s) = rep x [true, true, false] (cons true s) := by
  have h := rep_rotate x [true] [true, false, true] [true, true, false] rfl s
  simpa [app] using h

theorem round' (x y : Nat) (R : Tape) : steps (12 * x + 26) (cfg x (y + 5) R) = some (cfg (x + 2) (y + 1) R) := by
  have h := round x y R
  rw [rot] at h
  have e : rep (x + 2) [true, true, false] (rep (y + 1) [true] R)
      = app [true, true, false] (rep x [true, true, false] (app [true, true, false] (rep (y + 1) [true] R))) := by
    rw [rep_app_comm]; rfl
  simp only [cfg, e]
  exact h

/-- k rounds: (x, y + 4k + 1) -> (x + 2k, y + 1). -/
theorem rounds (k : Nat) : ∀ x y R, ∃ n, steps n (cfg x (y + 4 * k + 1) R) = some (cfg (x + 2 * k) (y + 1) R) := by
  induction k with
  | zero => intro x y R; exact ⟨0, rfl⟩
  | succ k ih =>
    intro x y R
    obtain ⟨n, hn⟩ := ih (x + 2) y R
    have e1 : y + 4 * (k + 1) + 1 = (y + 4 * k) + 5 := by omega
    have e2 : x + 2 + 2 * k = x + 2 * (k + 1) := by omega
    rw [e2] at hn
    rw [e1]
    have h1 := round' x (y + 4 * k) R
    exact ⟨_, steps_seq trans h1 hn⟩

end H126128
