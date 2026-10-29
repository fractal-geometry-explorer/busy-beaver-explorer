import Macro

/-!
# Long runs from blank tape, by the macro step

`runM_sound` makes a bounded run of the macro map a bounded run of the machine: if the first `m` macro steps from
blank tape are defined and take `t` machine steps, the machine does not halt in its first `t` steps.  The macro map
does a whole transfer phase in one arithmetic step, so this reaches far past the step-by-step `Blank.lean`.
-/

namespace BB6b

open TM

/-- The machine steps after `m` macro steps, or 0 if the macro run halted or got stuck. -/
def goSteps : Option Out → Nat
  | some (.go _ _ _ t) => t
  | _ => 0

theorem runs_of_runM (m N : Nat) (h : N ≤ goSteps (runM m)) : ∃ c, steps N init = some c := by
  cases e : runM m with
  | none => rw [e] at h; exact ⟨init, by rw [show N = 0 by simp [goSteps] at h; omega]; rfl⟩
  | some o =>
    cases o with
    | halt t => rw [e] at h; exact ⟨init, by rw [show N = 0 by simp [goSteps] at h; omega]; rfl⟩
    | go ls n cs t =>
      rw [e] at h
      have hs : steps t init = some (X ls n cs) := runM_sound m _ e
      rw [show t = N + (t - N) by simp only [goSteps] at h; omega] at hs
      exact steps_le trans hs

/-- A check against `py/macro.py` (its test `test_step_count`): 1,000 macro steps take 1,322,171 machine steps. -/
theorem runM_1000 : goSteps (runM 1000) = 1322171 := by decide +kernel

/-- 10⁵ macro steps: no halt in the first 2 · 10¹⁰ steps, checked by Lean's kernel alone (about a minute). -/
theorem blank_runs_2e10 : ∃ c, steps 20000000000 init = some c :=
  runs_of_runM 100000 _ (by decide +kernel)

/-- 10⁷ macro steps: no halt in the first 9 · 10¹³ steps, by compiled evaluation. -/
theorem blank_runs_9e13 : ∃ c, steps 90000000000000 init = some c :=
  runs_of_runM 10000000 _ (by native_decide)

end BB6b
