import Rules

/-!
# 1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA: a phase, by induction

`cfg n m R` is the record in B  `0^inf B> 0 0 1 (1100)^n (10110110)^m R`.  `period` (Rules.lean) trades five words
d = 10110110 for 31 words c = 1100 in 448n + 6952 steps; `periods q` chains q of them.  R is never read.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace H66813

open TM

/-- `0^inf B> 0 0 1 (1100)^n (10110110)^m R` -/
def cfg (n m : Nat) (R : Tape) : Config :=
  ⟨blank, cons false (cons false (cons true (rep n [true, true, false, false]
    (rep m [true, false, true, true, false, true, true, false] R)))), .B⟩

theorem pull (n : Nat) (s : Tape) :
    rep n [true, true, false, false] (cons true (cons true (cons false (cons false s))))
      = cons true (cons true (cons false (cons false (rep n [true, true, false, false] s)))) := by
  have h := rep_app_comm n [true, true, false, false] s
  simp only [app_cons, app_nil] at h
  rw [h, rep_succ]; rfl

/-- One period in the `cfg` form. -/
theorem period' (n m : Nat) (R : Tape) : steps (448 * n + 6952) (cfg n (m + 5) R) = some (cfg (n + 31) m R) := by
  have h := period m n R
  simp only [pull] at h
  simp only [cfg, rep_succ, app_cons, app_nil]
  exact h

/-- q periods: (n, m + 5q) -> (n + 31q, m). -/
theorem periods (q : Nat) : ∀ n m R, ∃ s, steps s (cfg n (m + 5 * q) R) = some (cfg (n + 31 * q) m R) := by
  induction q with
  | zero => intro n m R; exact ⟨0, rfl⟩
  | succ q ih =>
    intro n m R
    obtain ⟨s, hs⟩ := ih (n + 31) m R
    have e1 : m + 5 * (q + 1) = (m + 5 * q) + 5 := by omega
    have e2 : n + 31 + 31 * q = n + 31 * (q + 1) := by omega
    rw [e2] at hs
    rw [e1]
    exact ⟨_, steps_seq trans (period' n (m + 5 * q) R) hs⟩

end H66813
