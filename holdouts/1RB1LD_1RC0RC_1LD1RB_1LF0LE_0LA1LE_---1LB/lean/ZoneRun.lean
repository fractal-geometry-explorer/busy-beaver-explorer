import Zone

/-!
# 1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB: 3 · 10^7 steps of the zone orbit, by compiled evaluation

`zone_runs` (`native_decide`): the first 3 · 10^7 steps of the zone orbit (`Zone.lean`) do not halt and take more
than 1.7 · 10^15 machine steps; hence `blank_runs_zone`: no halt in the first 1.7 · 10^15 steps from blank tape.
The orbit keeps only the count of the block of words, so a sweep costs the depth of its pass in the zone, not the
length of the tape.
-/

namespace H117020

open TM

/-- Checked by compiled code: 3 · 10^7 steps of the zone orbit without a halt, more than 1.7 · 10^15 machine steps. -/
theorem zone_runs : (crun 30000000 (3, 0, [false], [])).any (fun p => decide (1700000000000000 ≤ p.1)) = true := by
  native_decide

theorem any_some' {α : Type} {o : Option α} {f : α → Bool} (h : o.any f = true) : ∃ a, o = some a ∧ f a = true := by
  cases o with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

/-- No halt in the first 1.7 · 10^15 steps from blank tape. -/
theorem blank_runs_zone : ∃ c, steps 1700000000000000 init = some c := by
  have hz := zone_runs
  rw [← corb_eq_crun] at hz
  obtain ⟨⟨t, n, Z, r⟩, hp, ht⟩ := any_some' hz
  have h := (corb_sound 30000000 t n Z r hp).1
  have ht' : 1700000000000000 ≤ t := of_decide_eq_true ht
  rw [show t = 1700000000000000 + (t - 1700000000000000) by omega] at h
  exact steps_le trans h

end H117020
