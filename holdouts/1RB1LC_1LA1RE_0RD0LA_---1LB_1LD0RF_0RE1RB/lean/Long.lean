import Cert

/-!
# 1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB: no halt in 1.2·10^70 steps

The certificate `cert.txt` (made by `py/accel.py cert`) is accepted by the checker of `Cert.lean`, so the machine
runs `N` ≈ 1.22·10^70 steps from blank tape without halting.
The check is one evaluation (`native_decide`, which trusts Lean's compiler); everything else is kernel-checked:
`checkCert_sound` turns any accepted certificate into a run of the machine.  `check.sh` evaluates it with the
checker compiled to a shared library (about 3 minutes); without it Lean's interpreter is far slower.
-/

namespace H56057

open TM

/-- The certificate: 60,256 operations, 20,226 of them batches of counter ticks. -/
def cert : String := include_str "cert.txt"

/-- The step count the certificate reaches. -/
def N : Nat := 12198487909209082368679859826732096416911140917107868420374132270946987

theorem cert_ok : checkCert cert = some N := by native_decide

/-- A run of `N` steps from blank tape. -/
theorem runs_N : ∃ c, steps N init = some c := checkCert_sound cert_ok

/-- No halt within the first `N` steps: every run of at most `N` steps from blank tape is defined. -/
theorem no_halt_within (n : Nat) (h : n ≤ N) : ∃ c, steps n init = some c := by
  obtain ⟨c, hc⟩ := runs_N
  exact steps_le trans (show steps (n + (N - n)) init = some c by rw [show n + (N - n) = N by omega]; exact hc)

/-- If the machine halts from blank tape, it does so after more than `N` steps: the halting configuration is
reached after at least `N` ordinary steps (so the halt is at step `N + 1` or later in the bbchallenge count). -/
theorem halt_late (n : Nat) (c : Config) (h₁ : steps n init = some c) (h₂ : step c = none) : N ≤ n := by
  apply Nat.le_of_not_lt
  intro hn
  obtain ⟨c', hc'⟩ := runs_N
  have := steps_halt trans h₁ h₂ (N - n - 1)
  rw [show n + (N - n - 1 + 1) = N by omega] at this
  have h3 : steps N init = none := this
  rw [h3] at hc'
  cases hc'

end H56057
