import Sound

/-!
# 1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE: halting is a question about the block machine

* `init_cfg`: from blank tape the machine reaches `cfg s0`, `1^10 F>0 0 1^3`, after 102 steps.
* `inv_next`: the invariant `InvQ` (no left block of 1; at an even left block other than 0 nothing sits between the
  units; at a left block of 2 something is right of the gap) is kept by the macro machine, which never gets `stuck`
  under it (`mstep_ne_stuck`): the rules of `Macro.lean` cover the whole run.
* `halts_iff`: **the machine halts from blank tape if and only if the macro machine reaches `halt`**.
* `mstep_halt_iff`: the macro machine halts exactly at `X = 4` with nothing but units right of the gap.
* `halts_iff_four`: so the machine halts if and only if the run reaches a configuration `1^4 F>0 0 (1 0)^k 0^∞`.

Everything is checked by Lean's kernel.
-/

namespace H15252

open TM

/-- The first macro configuration: `1^10 F>0 0 1^3`. -/
def s0 : Q := ⟨10, 0, .none, 0, some 0⟩

theorem init_cfg : steps 102 init = some (cfg s0) := by
  have h : steps 102 init = some ⟨rep 10 [true] blank, cons false (cons false (rep 3 [true] blank)), .F⟩ := by
    rw [show (⟨rep 10 [true] blank, cons false (cons false (rep 3 [true] blank)), .F⟩ : Config) =
      (FCfg.toCfg ⟨List.replicate 10 true, [false, false, true, true, true], .F⟩) from rfl]
    exact blank_reaches trans (by decide)
  exact h

/-- The invariant. -/
def InvQ (s : Q) : Prop :=
  s.X ≠ 1 ∧ (s.X % 2 = 0 → s.X ≠ 0 → s.m = .none) ∧ (s.X = 2 → s.a + s.b ≠ 0 ∨ s.t ≠ none)

theorem inv_s0 : InvQ s0 := by simp [InvQ, s0]

theorem inv_norm (s : Q) (h2 : s.X % 2 = 0 → s.X ≠ 0 → s.m = .none) (h3 : s.X = 2 → s.a + s.b ≠ 0 ∨ s.t ≠ none) :
    InvQ (norm s).1 := by
  unfold norm
  split
  · simp [InvQ]
  · exact ⟨by assumption, h2, h3⟩

/-- The invariant is kept, and under it the macro machine is never stuck. -/
theorem inv_next (s : Q) (h : InvQ s) : mstep s ≠ .stuck ∧ ∀ s' n, mstep s = .go s' n → InvQ s' := by
  obtain ⟨X, a, m, b, t⟩ := s
  obtain ⟨h1, h2, h3⟩ := h
  simp only at h1 h2 h3
  cases m with
  | ev q =>
    have hodd : X % 2 = 1 ∨ X = 0 := by
      rcases Nat.mod_two_eq_zero_or_one X with h | h
      · by_cases hx : X = 0
        · exact Or.inr hx
        · exact absurd (h2 h hx) (by simp)
      · exact Or.inl h
    simp only [mstep]
    split
    · refine ⟨by simp [withNorm], fun s' n hs => ?_⟩
      simp only [withNorm, MS.go.injEq] at hs; obtain ⟨rfl, -⟩ := hs
      exact inv_norm _ (by first | (simp; omega) | simp | omega) (by first | (simp; omega) | simp | omega)
    · split
      · refine ⟨by simp, fun s' n hs => ?_⟩
        simp only [MS.go.injEq] at hs; obtain ⟨rfl, -⟩ := hs
        simp [InvQ]
      · omega
  | none =>
    cases t with
    | some q =>
      simp only [mstep]
      split
      · subst_vars
        split
        · refine ⟨by simp, fun s' n hs => ?_⟩
          simp only [MS.go.injEq] at hs; obtain ⟨rfl, -⟩ := hs; simp [InvQ]
        · refine ⟨by simp, fun s' n hs => ?_⟩
          simp only [MS.go.injEq] at hs; obtain ⟨rfl, -⟩ := hs; simp [InvQ]
      · split
        · refine ⟨by simp [withNorm], fun s' n hs => ?_⟩
          simp only [withNorm, MS.go.injEq] at hs; obtain ⟨rfl, -⟩ := hs
          cases q <;> exact inv_norm _ (by simp [tailNext]) (by simp [tailNext])
        · split
          · refine ⟨by simp, fun s' n hs => ?_⟩
            simp only [MS.go.injEq] at hs; obtain ⟨rfl, -⟩ := hs
            cases q <;> simp [InvQ, tailNext]
          · omega
    | none =>
      simp only [mstep]
      split
      · subst_vars
        split
        · rename_i hab; simp at h3; omega
        · refine ⟨by simp, fun s' n hs => ?_⟩
          simp only [MS.go.injEq] at hs; obtain ⟨rfl, -⟩ := hs; simp [InvQ]
      · split
        · refine ⟨by simp [withNorm], fun s' n hs => ?_⟩
          simp only [withNorm, MS.go.injEq] at hs; obtain ⟨rfl, -⟩ := hs
          exact inv_norm _ (by simp) (by simp)
        · split
          · exact ⟨by simp, fun s' n hs => by cases hs⟩
          · split
            · refine ⟨by simp, fun s' n hs => ?_⟩
              simp only [MS.go.injEq] at hs; obtain ⟨rfl, -⟩ := hs; simp [InvQ]
            · split
              · refine ⟨by simp, fun s' n hs => ?_⟩
                simp only [MS.go.injEq] at hs; obtain ⟨rfl, -⟩ := hs; simp [InvQ]
              · omega
  | zero =>
    have hodd : X % 2 = 1 ∨ X = 0 := by
      rcases Nat.mod_two_eq_zero_or_one X with h | h
      · by_cases hx : X = 0
        · exact Or.inr hx
        · exact absurd (h2 h hx) (by simp)
      · exact Or.inl h
    simp only [mstep]
    split
    · split <;> refine ⟨by simp [withNorm], fun s' n hs => ?_⟩ <;>
        simp only [withNorm, MS.go.injEq] at hs <;> obtain ⟨rfl, -⟩ := hs <;>
        exact inv_norm _ (by first | (simp; omega) | simp | omega) (by first | (simp; omega) | simp | omega)
    · split
      · split <;> refine ⟨by simp, fun s' n hs => ?_⟩ <;>
          simp only [MS.go.injEq] at hs <;> obtain ⟨rfl, -⟩ := hs <;> simp [InvQ] <;> omega
      · omega

/-! ## Runs -/

/-- One macro step on a run: the configuration and the machine steps so far. -/
def mnext : MS → MS
  | .go s t => match mstep s with
    | .go s' k => .go s' (t + k)
    | x => x
  | x => x

def mrun : Nat → MS → MS
  | 0, x => x
  | n + 1, x => mrun n (mnext x)

theorem mrun_succ' : ∀ (n : Nat) (x : MS), mrun (n + 1) x = mnext (mrun n x)
  | 0, _ => rfl
  | n + 1, x => by rw [mrun, mrun_succ' n (mnext x)]; rfl

/-- The run from the first macro configuration, 102 steps in. -/
def m0 : MS := .go s0 102

/-- The run stays inside the invariant and never gets stuck; each configuration is reached by the machine at the
step count it carries. -/
theorem mrun_inv : ∀ n, (∃ s t, mrun n m0 = .go s t ∧ InvQ s ∧ steps t init = some (cfg s)) ∨ mrun n m0 = .halt
  | 0 => Or.inl ⟨s0, 102, rfl, inv_s0, init_cfg⟩
  | n + 1 => by
    rw [mrun_succ']
    rcases mrun_inv n with ⟨s, t, hm, hi, hs⟩ | hm
    · rw [hm]
      obtain ⟨hns, hpres⟩ := inv_next s hi
      simp only [mnext]
      cases hst : mstep s with
      | go s' k => exact Or.inl ⟨s', t + k, rfl, hpres s' k hst, steps_seq trans hs (mstep_sound s hst)⟩
      | halt => exact Or.inr rfl
      | stuck => exact absurd hst hns
    · rw [hm]; exact Or.inr rfl

theorem mcost_pos {s s' : Q} {k : Nat} (h : mstep s = .go s' k) : 1 ≤ k := by
  obtain ⟨X, a, m, b, t⟩ := s
  cases m <;> (try cases t) <;> simp only [mstep, withNorm] at h <;>
    (repeat' split at h) <;> (try simp only [MS.go.injEq] at h) <;> (try cases h) <;>
    (try (rename_i h'; obtain ⟨-, rfl⟩ := h'; omega)) <;> (try omega)

theorem mrun_t : ∀ n, ∀ s t, mrun n m0 = .go s t → 102 + n ≤ t
  | 0 => fun s t h => by cases h; omega
  | n + 1 => fun s t h => by
    rw [mrun_succ'] at h
    rcases mrun_inv n with ⟨s1, t1, hm, -, -⟩ | hm
    · rw [hm] at h
      have := mrun_t n s1 t1 hm
      simp only [mnext] at h
      cases hst : mstep s1 with
      | go s' k =>
        rw [hst] at h; simp only [MS.go.injEq] at h; obtain ⟨-, rfl⟩ := h
        have := mcost_pos hst; omega
      | halt => rw [hst] at h; cases h
      | stuck => rw [hst] at h; cases h
    · rw [hm] at h; cases h

theorem halts_of_steps {k : Nat} {c c' : Config} (h : steps k c = some c') (h' : Halts trans c') :
    Halts trans c := by
  obtain ⟨n, d, hd, hs⟩ := h'
  exact ⟨k + n, d, steps_seq trans h hd, hs⟩

theorem halts_of_mrun : ∀ n, mrun n m0 = .halt → HaltsFromBlank
  | 0, hn => by cases hn
  | n + 1, hn => by
    rw [mrun_succ'] at hn
    rcases mrun_inv n with ⟨s, t, hm, -, hs⟩ | hm
    · rw [hm] at hn
      simp only [mnext] at hn
      cases hst : mstep s with
      | go s' k => rw [hst] at hn; cases hn
      | halt =>
        obtain ⟨k, c, hk, hc⟩ := mstep_halt s hst
        exact halts_of_steps hs ⟨k, c, hk, hc⟩
      | stuck => rw [hst] at hn; cases hn
    · exact halts_of_mrun n hm

/-- **The reduction.**  The machine halts from blank tape if and only if the macro machine reaches `halt`. -/
theorem halts_iff : HaltsFromBlank ↔ ∃ n, mrun n m0 = .halt := by
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hN
    refine not_halts_of_forall trans (forall_of_unbounded trans (fun m => ∃ c, steps m init = some c) ?_ ?_) hH
    · intro n
      rcases mrun_inv n with ⟨s, t, hm, -, hs⟩ | hm
      · exact ⟨t, by have := mrun_t n s t hm; omega, _, hs⟩
      · exact absurd ⟨n, hm⟩ hN
    · intro m hm; exact hm
  · rintro ⟨n, hn⟩; exact halts_of_mrun n hn

/-- Under the invariant, the macro machine halts exactly at `X = 4` with only units right of the gap. -/
theorem mstep_halt_iff (s : Q) : mstep s = .halt ↔ s.X = 4 ∧ s.m = .none ∧ s.t = none := by
  obtain ⟨X, a, m, b, t⟩ := s
  constructor
  · intro h
    cases m with
    | ev q =>
      simp only [mstep, withNorm] at h
      repeat' split at h
      all_goals cases h
    | none =>
      cases t with
      | some q =>
        simp only [mstep, withNorm] at h
        repeat' split at h
        all_goals cases h
      | none =>
        simp only [mstep, withNorm] at h
        repeat' split at h
        all_goals (cases h; try (subst_vars; simp))
    | zero =>
      simp only [mstep, withNorm] at h
      repeat' split at h
      all_goals cases h
  · rintro ⟨rfl, rfl, rfl⟩; rfl

/-- **Where it halts.**  The machine halts from blank tape if and only if the run reaches a configuration
`1^4 F>0 0 (1 0)^k 0^∞`: a left block of exactly four 1s when nothing but units is left right of the gap. -/
theorem halts_iff_four : HaltsFromBlank ↔ ∃ n t a b, mrun n m0 = .go ⟨4, a, .none, b, none⟩ t := by
  rw [halts_iff]
  constructor
  · rintro ⟨n, hn⟩
    -- the first halt comes from a `go` step
    induction n with
    | zero => cases hn
    | succ n ih =>
      rw [mrun_succ'] at hn
      rcases mrun_inv n with ⟨s, t, hm, -, -⟩ | hm
      · rw [hm] at hn
        simp only [mnext] at hn
        cases hst : mstep s with
        | go s' k => rw [hst] at hn; cases hn
        | halt =>
          obtain ⟨h4, hmn, htn⟩ := (mstep_halt_iff s).mp hst
          obtain ⟨X, a, m, b, tt⟩ := s
          simp only at h4 hmn htn; subst h4 hmn htn
          exact ⟨n, t, a, b, hm⟩
        | stuck => rw [hst] at hn; cases hn
      · exact ih hm
  · rintro ⟨n, t, a, b, h⟩
    exact ⟨n + 1, by rw [mrun_succ', h]; rfl⟩

end H15252
