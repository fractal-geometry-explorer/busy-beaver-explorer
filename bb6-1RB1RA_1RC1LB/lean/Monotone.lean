import Wave

/-!
# N grows at every super step

`N = bigN L = 10 + Σ p_l 2^{m-l}` decides halting (`superL_none_iff`, `halts_iff_pow2'`). This file proves that it
strictly increases at every super step that does not halt (`superL_grows`), so along the orbit from blank tape it is
strictly increasing (`orbit_grows`): the orbit passes each power of two once, landing on it or jumping over it.

* At the left end (`leftEnd_grows`) the new blocks `S W` are more than `3/2` of the arriving `d`.
* Through the blocks (`wave_grows`): with the blocks `L` further left, `d + 2 S L < S W`. Where the wave turns (`d`
  odd) the gain is `(d + 3) / 2`; where it passes (`d` even) the gain below adds `d / 2`.

So, read with `Wave.lean`: between two returns to the left end the number of blocks is fixed and `N` grows, so at the
next return `d_1 = N / 2^(m-1)` is larger than `N / 2^(m-1)` now, which is at least `p_1 + p_2 / 2 + p_3 / 4 + …` for
the blocks now.
-/

namespace BB6b

theorem leftEnd_grows : ∀ (f d : Nat) (W : List Nat), leftEnd f d = some W → 3 * d < 2 * S W := by
  intro f
  induction f with
  | zero => intro d W h; simp [leftEnd] at h
  | succ f ih =>
    intro d W h
    by_cases h₁ : d ≤ 1
    · simp [leftEnd, h₁] at h
    rcases Nat.mod_two_eq_zero_or_one d with hd | hd
    · rw [leftEnd_even f d (by omega) hd] at h
      cases e : leftEnd f (d / 2) with
      | none => rw [e] at h; simp at h
      | some W' =>
        rw [e] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        have := ih (d / 2) W' e
        simp only [S]
        omega
    · rw [leftEnd_odd f d (by omega) hd] at h
      simp only [Option.some.injEq] at h
      subst h
      simp only [S]
      omega

theorem wave_grows : ∀ (L : List Nat) (d : Nat) (W : List Nat), wave d L = some W → d + 2 * S L < S W := by
  intro L
  induction L with
  | nil =>
    intro d W h
    have := leftEnd_grows d d W h
    simp only [S]
    omega
  | cons p L ih =>
    intro d W h
    rcases Nat.mod_two_eq_zero_or_one d with hd | hd
    · rw [wave_even d p L hd] at h
      cases e : wave (p + d / 2) L with
      | none => rw [e] at h; simp at h
      | some W' =>
        rw [e] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        have := ih (p + d / 2) W' e
        simp only [S]
        omega
    · rw [wave_odd d p L hd] at h
      simp only [Option.some.injEq] at h
      subst h
      simp only [S]
      omega

/-- **N strictly increases at every super step.** -/
theorem superL_grows (L W : List Nat) (h : superL L = some W) : bigN L < bigN W := by
  match L with
  | [] => simp [superL] at h
  | p :: L =>
    have := wave_grows L (p + 10) W h
    simp only [bigN, S]
    omega

theorem orbit_succ' : ∀ (j : Nat) (L : List Nat), orbit (j + 1) L = (orbit j L).bind superL := by
  intro j
  induction j with
  | zero => intro L; simp [orbit]
  | succ j ih =>
    intro L
    rw [orbit, orbit]
    cases superL L with
    | none => rfl
    | some W => simp only [Option.bind_some]; exact ih W

/-- **Along the orbit, N is strictly increasing**: each power of two is reached at most once. -/
theorem orbit_grows (L : List Nat) : ∀ (j k : Nat) (W W' : List Nat), orbit j L = some W →
    orbit (j + k + 1) L = some W' → bigN W < bigN W' := by
  intro j k
  induction k generalizing j with
  | zero =>
    intro W W' h₁ h₂
    rw [orbit_succ', h₁] at h₂
    exact superL_grows W W' h₂
  | succ k ih =>
    intro W W' h₁ h₂
    rw [show j + (k + 1) + 1 = (j + k + 1) + 1 by omega, orbit_succ'] at h₂
    cases e : orbit (j + k + 1) L with
    | none => rw [e] at h₂; simp at h₂
    | some V =>
      rw [e] at h₂
      exact Nat.lt_trans (ih j W V h₁ e) (superL_grows V W' h₂)

/-- On the orbit from blank tape (`halts_iff_pow2`), `N` at a later super step is larger. -/
theorem blank_orbit_grows (j k : Nat) (W W' : List Nat) (h₁ : orbit j [6, 1] = some W)
    (h₂ : orbit (j + k + 1) [6, 1] = some W') : bigN W < bigN W' :=
  orbit_grows [6, 1] j k W W' h₁ h₂

end BB6b
