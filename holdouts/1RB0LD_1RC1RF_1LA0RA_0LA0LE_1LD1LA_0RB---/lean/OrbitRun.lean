import Reduce

/-!
# 1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---: the first 10,000 macro steps, by compiled evaluation

`orbT n` is the orbit with the machine's step count; `orbT_sound` (kernel) says it is a run of the machine.
`orbit_runs` (`native_decide`): the first 10,000 macro steps stay inside the rules and take more than 10^2400 machine
steps, so the machine does not halt in its first 10^2400 steps (`blank_runs_orbit`).
-/

namespace H141950

open TM

/-- The orbit with the machine step count at each wall. -/
def orbT : Nat → Option (Nat × Nat × Nat)
  | 0 => some (0, 0, 7)
  | n + 1 => (orbT n).bind (fun p => (next p.1 p.2.1).map (fun q => (q.1, q.2, p.2.2 + mcost p.1 p.2.1)))

theorem orbT_sound : ∀ (n z y t : Nat), orbT n = some (z, y, t) → steps t init = some (C z y) ∧ orb n = some (z, y)
  | 0, z, y, t, h => by
    simp only [orbT, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨init_wall, rfl⟩
  | n + 1, z, y, t, h => by
    simp only [orbT] at h
    cases hp : orbT n with
    | none => rw [hp] at h; cases h
    | some p =>
      obtain ⟨z0, y0, t0⟩ := p
      rw [hp, Option.bind_some] at h
      cases hx : next z0 y0 with
      | none => rw [hx] at h; cases h
      | some q =>
        obtain ⟨z1, y1⟩ := q
        rw [hx] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨ht, ho⟩ := orbT_sound n z0 y0 t0 hp
        exact ⟨steps_seq trans ht (next_sound hx), by simp only [orb, ho, Option.bind_some, hx]⟩

/-- Checked by compiled code: 10,000 macro steps inside the rules, more than 10^2400 machine steps. -/
theorem orbit_runs : (orbT 10000).any (fun p => decide (10 ^ 2400 ≤ p.2.2)) = true := by native_decide

theorem any_some {α : Type} {o : Option α} {f : α → Bool} (h : o.any f = true) : ∃ a, o = some a ∧ f a = true := by
  cases o with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

theorem orb_none_succ {n : Nat} (h : orb n = none) : orb (n + 1) = none := by simp [orb, h]

/-- The first 10,000 macro configurations exist (the orbit has not left the rules). -/
theorem orb_some_10000 : ∀ n ≤ 10000, orb n ≠ none := by
  obtain ⟨⟨z, y, t⟩, hp, _⟩ := any_some orbit_runs
  have h := (orbT_sound 10000 z y t hp).2
  intro n hn hnone
  have : ∀ k, orb (n + k) = none := fun k => by
    induction k with
    | zero => exact hnone
    | succ k ih => exact orb_none_succ ih
  have := this (10000 - n)
  rw [show n + (10000 - n) = 10000 by omega, h] at this
  cases this

/-- No halt in the first 10^2400 steps from blank tape. -/
theorem blank_runs_orbit : ∃ c, steps (10 ^ 2400) init = some c := by
  obtain ⟨⟨z, y, t⟩, hp, ht⟩ := any_some orbit_runs
  have h := (orbT_sound 10000 z y t hp).1
  have ht' : 10 ^ 2400 ≤ t := of_decide_eq_true ht
  rw [show t = 10 ^ 2400 + (t - 10 ^ 2400) by omega] at h
  exact steps_le trans h

end H141950
