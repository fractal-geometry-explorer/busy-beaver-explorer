import Orbit

/-!
# One theorem for both directions

`pstep_never_unknown`: the fuel `2n + 2` in `pstep` always suffices, so a macro step either reaches the next `P n'`
or halts.  With `pstep_sound` this gives `halts_iff`: the machine halts from blank tape if and only if the orbit of
`pstep` from `P 4` stops (`orbit k 4 = none` for some `k`).
-/

namespace H50372

open TM

theorem addT_ne_unknown {a : Nat} {o : Out} (h : o ≠ .unknown) : o.addT a ≠ .unknown := by
  cases o <;> simp [Out.addT] at h ⊢

theorem tend_ne_unknown (c m : Nat) : tend c m ≠ .unknown := by
  intro h
  simp only [tend] at h
  repeat' split at h
  all_goals cases h

theorem tphase_ne_unknown : ∀ f c m, m ≤ f + 2 * c + 5 → tphase f c m ≠ .unknown := by
  intro f
  induction f with
  | zero =>
    intro c m hm
    simp only [tphase]
    rw [if_neg (show ¬ 2 * c + 6 ≤ m by omega)]
    exact tend_ne_unknown c m
  | succ f ih =>
    intro c m hm
    simp only [tphase]
    by_cases h : 2 * c + 6 ≤ m
    · rw [if_pos h]
      exact addT_ne_unknown (ih _ _ (by omega))
    · rw [if_neg h]; exact tend_ne_unknown c m

/-- The fuel in `pstep` never runs out. -/
theorem pstep_never_unknown (n : Nat) : pstep n ≠ .unknown :=
  addT_ne_unknown (tphase_ne_unknown _ _ _ (by omega))

/-- A macro step that does not halt takes at least 8 steps. -/
theorem pstep_go_ge {n n' t : Nat} (h : pstep n = .go n' t) : 8 ≤ t := by
  unfold pstep at h
  generalize tphase (2 * n + 2) 1 (2 * n + 2) = o at h
  cases o <;> simp [Out.addT] at h
  omega

/-- If the orbit has not stopped after `k` macro steps, they took at least `k` steps. -/
theorem orbit_steps_ge : ∀ k n n' t, orbit k n = some (n', t) → k ≤ t := by
  intro k
  induction k with
  | zero => intro _ _ _ _; omega
  | succ k ih =>
    intro n n' t h
    unfold orbit at h
    revert h
    cases e : pstep n with
    | halt _ => intro h; cases h
    | unknown => intro h; cases h
    | go m t₁ =>
      intro h
      simp only at h
      cases e2 : orbit k m with
      | none => rw [e2] at h; cases h
      | some p =>
        rw [e2] at h
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        have := ih m p.1 p.2 (by rw [e2])
        have := pstep_go_ge e
        omega

/-- If the orbit from `P n` stops, the machine halts from `P n`. -/
theorem halts_of_orbit_none : ∀ k n, orbit k n = none → Halts trans (P n) := by
  intro k
  induction k with
  | zero => intro n h; simp [orbit] at h
  | succ k ih =>
    intro n h
    have hs := pstep_sound n
    have hu := pstep_never_unknown n
    unfold orbit at h
    cases e : pstep n with
    | halt t => rw [e] at hs; obtain ⟨c', h₁, h₂⟩ := hs; exact ⟨t, c', h₁, h₂⟩
    | unknown => exact absurd e hu
    | go m t₁ =>
      rw [e] at hs h
      simp only at h
      cases e2 : orbit k m with
      | some p => rw [e2] at h; cases h
      | none =>
        obtain ⟨j, c', h₁, h₂⟩ := ih m e2
        exact ⟨t₁ + j, c', steps_seq trans hs h₁, h₂⟩

/-- **The reduction in both directions.**  The machine halts from blank tape if and only if the orbit of the macro
step `pstep` from `P 4` stops, that is, some macro step halts. -/
theorem halts_iff : HaltsFromBlank ↔ ∃ k, orbit k 4 = none := by
  constructor
  · intro hb
    apply Classical.byContradiction
    intro hn
    apply not_halts_of_forall trans _ hb
    apply forall_of_unbounded trans (fun m => ∃ k, m = 31 + orbitT k ∧ (orbit k 4).isSome = true)
    · intro N
      have hs : (orbit N 4).isSome = true := by
        cases e : orbit N 4 with
        | none => exact absurd ⟨N, e⟩ hn
        | some _ => rfl
      refine ⟨31 + orbitT N, ?_, N, rfl, hs⟩
      cases e : orbit N 4 with
      | none => rw [e] at hs; cases hs
      | some p =>
        obtain ⟨n', t⟩ := p
        have := orbit_steps_ge N 4 n' t e
        simp only [orbitT, e]; omega
    · rintro m ⟨k, rfl, hk⟩
      exact no_halt_of_orbitT k hk
  · rintro ⟨k, hk⟩
    obtain ⟨j, c', h₁, h₂⟩ := halts_of_orbit_none k 4 hk
    exact ⟨31 + j, c', steps_seq trans init_P4 h₁, h₂⟩

end H50372
