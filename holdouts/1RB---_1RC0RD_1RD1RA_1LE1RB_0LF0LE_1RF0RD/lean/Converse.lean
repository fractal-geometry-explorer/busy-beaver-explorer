import Family

/-!
# Halting is exactly the phase map getting stuck

`halts_iff_stuck`: the machine halts from blank tape **if and only if** the orbit of `phase` from `(0, 2, 2)` gets
stuck, and `halts_iff_family`: if and only if the orbit meets `(m, m + 2, 2^(m+1) + 1)` for some `m`.

One direction is `not_halts_of_orbit` (`Orbit.lean`).  For the other: every configuration of the orbit up to the
first one of the family is `Good` (`2 ≤ Y < 2^M`, `d + 1 ≤ M`); outside the family `phase` always returns a
configuration (`phase_some`, `Start.lean`); so the orbit gets stuck only after meeting the family, and the family
halts (`fam_halts`, `Family.lean`).
-/

namespace H140108

open TM

/-- The orbit meets the halting family. -/
def FamMet : Prop := ∃ k m, orbit k = some (m, m + 2, 2 ^ (m + 1) + 1)

theorem famMet_of {n d M Y : Nat} (ho : orbit n = some (d, M, Y)) (hf : Fam d M Y) : FamMet := by
  obtain ⟨e1, e2⟩ := hf
  subst e1
  rw [show d + 2 - 1 = d + 1 by omega] at e2
  subst e2
  exact ⟨n, d, ho⟩

theorem halts_of_famMet (h : FamMet) : HaltsFromBlank := by
  obtain ⟨n, m, ho⟩ := h
  obtain ⟨t, -, hs⟩ := orbit_reach n _ _ _ ho
  obtain ⟨c, ⟨u, hu⟩, hc⟩ := fam_halts m
  exact ⟨t + u, c, TM.steps_seq trans hs hu, hc⟩

theorem orbit_good : ∀ n d M Y, orbit n = some (d, M, Y) → Good d M Y ∨ FamMet
  | 0, d, M, Y, h => by
    simp only [orbit, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Or.inl ⟨by omega, by decide, by omega⟩
  | n + 1, d1, M1, Y1, h => by
    cases ho : orbit n with
    | none => simp [orbit, ho] at h
    | some x =>
      obtain ⟨d, M, Y⟩ := x
      rcases orbit_good n d M Y ho with hg | hm
      · by_cases hf : Fam d M Y
        · exact Or.inr (famMet_of ho hf)
        · obtain ⟨d', M', Y', hp, hg'⟩ := phase_some hg hf
          simp only [orbit, ho, hp, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact Or.inl hg'
      · exact Or.inr hm

/-- The orbit gets stuck only after it has met the family. -/
theorem famMet_of_stuck : ∀ n, orbit n = none → FamMet
  | 0, h => by simp [orbit] at h
  | n + 1, h => by
    cases ho : orbit n with
    | none => exact famMet_of_stuck n ho
    | some x =>
      obtain ⟨d, M, Y⟩ := x
      rcases orbit_good n d M Y ho with hg | hm
      · by_cases hf : Fam d M Y
        · exact famMet_of ho hf
        · obtain ⟨d', M', Y', hp, -⟩ := phase_some hg hf
          simp [orbit, ho, hp] at h
      · exact hm

/-- **The machine halts from blank tape if and only if the orbit of the phase map gets stuck.** -/
theorem halts_iff_stuck : HaltsFromBlank ↔ ∃ n, orbit n = none := by
  constructor
  · intro h
    exact Classical.byContradiction fun hn => not_halts_of_orbit (fun n hn' => hn ⟨n, hn'⟩) h
  · rintro ⟨n, hn⟩
    exact halts_of_famMet (famMet_of_stuck n hn)

/-- **The machine halts from blank tape if and only if the orbit meets `(m, m + 2, 2^(m+1) + 1)`.** -/
theorem halts_iff_family : HaltsFromBlank ↔ ∃ n m, orbit n = some (m, m + 2, 2 ^ (m + 1) + 1) := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := halts_iff_stuck.mp h
    exact famMet_of_stuck n hn
  · exact halts_of_famMet

end H140108
