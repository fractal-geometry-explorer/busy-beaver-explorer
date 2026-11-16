import Reduce

/-!
# 1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA: the first 20,000 macro steps, by compiled evaluation

`orbit_runs` (`native_decide`): the first 20,000 macro steps of the pass orbit do not halt and take more than
4 · 10^8 machine steps (the orbit goes through the first five resets of the left end, the last near macro step 8,520);
hence `blank_runs_orbit`: no halt in the first 4 · 10^8 steps from blank tape.
-/

namespace H73071

open TM

/-- Checked by compiled code: 20,000 macro steps without a halt, more than 4 · 10^8 machine steps. -/
theorem orbit_runs : (orbT 20000).any (fun p => decide (400000000 ≤ p.2.2)) = true := by native_decide

theorem any_some {α : Type} {o : Option α} {f : α → Bool} (h : o.any f = true) : ∃ a, o = some a ∧ f a = true := by
  cases o with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

/-- No halt in the first 4 · 10^8 steps from blank tape. -/
theorem blank_runs_orbit : ∃ c, steps 400000000 init = some c := by
  obtain ⟨⟨o, r, t⟩, hp, ht⟩ := any_some orbit_runs
  have h := (orbT_sound 20000 o r t hp).1
  have ht' : 400000000 ≤ t := of_decide_eq_true ht
  rw [show t = 400000000 + (t - 400000000) by omega] at h
  exact steps_le trans h

end H73071
