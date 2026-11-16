import Reduce

/-!
# 1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA: the first 15,000 macro steps, by compiled evaluation

`orbit_runs` (`native_decide`): the first 15,000 macro steps of the orbit do not halt and take more than
4 · 10^8 machine steps (the orbit goes through the six resets of the left end, the last near macro step 56);
hence `blank_runs_orbit`: no halt in the first 4 · 10^8 steps from blank tape.
-/

namespace H25821

open TM

/-- Checked by compiled code: 15,000 macro steps without a halt, more than 4 · 10^8 machine steps. -/
theorem orbit_runs : (orbT 15000).any (fun p => decide (400000000 ≤ p.2)) = true := by native_decide

theorem any_some {α : Type} {o : Option α} {f : α → Bool} (h : o.any f = true) : ∃ a, o = some a ∧ f a = true := by
  cases o with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

/-- No halt in the first 4 · 10^8 steps from blank tape. -/
theorem blank_runs_orbit : ∃ c, steps 400000000 init = some c := by
  obtain ⟨⟨s, t⟩, hp, ht⟩ := any_some orbit_runs
  have h := (orbT_sound 15000 s t hp).1
  have ht' : 400000000 ≤ t := of_decide_eq_true ht
  rw [show t = 400000000 + (t - 400000000) by omega] at h
  exact steps_le trans h

end H25821
