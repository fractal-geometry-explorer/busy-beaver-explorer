import Map

/-!
# The run from blank tape, E-event by E-event

`init_E`: the run from blank tape is at the E-event `Ev 0 .one` after 18 steps.  `orbit k T n` applies the map
`next` (proved in `Map.lean`) `k` times from `Ev n T` and returns where it is and how many steps it took, or `none`
if the map is undefined on the way (a Z-event with `n < 12k + 12`).  `orbit_sound` turns a value of `orbit` into a
statement about the machine; the theorems at the end evaluate it, in the kernel and with `native_decide`.
-/

namespace H70770

open TM

theorem init_E : steps 18 init = some (Ev 0 .one) :=
  blank_reaches trans (q := St.A) (n := 18) (c := ⟨[], [false, false, false, false, false, false, true], .E⟩)
    (by decide +kernel)

/-- `k` E-steps from `Ev n T`: the end and the number of steps, or `none` if the map is undefined on the way. -/
def orbit : Nat → Tail → Nat → Option (Tail × Nat × Nat)
  | 0, T, n => some (T, n, 0)
  | k + 1, T, n =>
    match next T n with
    | some (T', n', s) => (orbit k T' n').map (fun p => (p.1, p.2.1, s + p.2.2))
    | none => none

theorem orbit_sound : ∀ k T n T' n' t, orbit k T n = some (T', n', t) → steps t (Ev n T) = some (Ev n' T') := by
  intro k
  induction k with
  | zero => intro T n T' n' t h; simp [orbit] at h; obtain ⟨rfl, rfl, rfl⟩ := h; rfl
  | succ k ih =>
    intro T n T' n' t h
    unfold orbit at h
    cases e : next T n with
    | none => rw [e] at h; cases h
    | some q =>
      obtain ⟨T₁, n₁, s⟩ := q
      rw [e] at h
      dsimp only at h
      cases e2 : orbit k T₁ n₁ with
      | none => rw [e2] at h; cases h
      | some p =>
        rw [e2] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨T₂, n₂, t₂⟩ := p
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact steps_seq trans (next_sound T n T₁ n₁ s e) (ih T₁ n₁ T₂ n₂ t₂ e2)

/-- The number of steps of `k` E-steps from blank tape (0 if the map is undefined on the way). -/
def orbitT (k : Nat) : Nat := match orbit k .one 0 with | some p => 18 + p.2.2 | none => 0

/-- No halt in the first `n ≤ orbitT k` steps when the first `k` E-steps from blank tape are covered by the map. -/
theorem no_halt_of_orbit (k : Nat) (h : (orbit k .one 0).isSome = true) (n : Nat) (hn : n ≤ orbitT k) :
    ∃ c, steps n init = some c := by
  cases e : orbit k .one 0 with
  | none => rw [e] at h; cases h
  | some p =>
    obtain ⟨T, m, t⟩ := p
    have hr := steps_seq trans init_E (orbit_sound k .one 0 T m t e)
    simp only [orbitT, e] at hn
    exact steps_le trans (show steps (n + (18 + t - n)) init = _ by rw [show n + (18 + t - n) = 18 + t by omega]; exact hr)

theorem orbit_steps_ge : ∀ k T n T' n' t, orbit k T n = some (T', n', t) → k ≤ t := by
  intro k
  induction k with
  | zero => intro T n T' n' t _; exact Nat.zero_le _
  | succ k ih =>
    intro T n T' n' t h
    unfold orbit at h
    cases e : next T n with
    | none => rw [e] at h; cases h
    | some q =>
      obtain ⟨T₁, n₁, s⟩ := q
      rw [e] at h
      dsimp only at h
      cases e2 : orbit k T₁ n₁ with
      | none => rw [e2] at h; cases h
      | some p =>
        rw [e2] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨T₂, n₂, t₂⟩ := p
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have h1 := next_pos T n T₁ n₁ s e
        have h2 := ih T₁ n₁ T₂ n₂ t₂ e2
        omega

/-- **Non-halting reduces to the map.** If the orbit of `next` from blank tape never gets stuck (never reaches a
Z-event `Ev n (.Z k)` with `k = 0` or `n < 12k + 12`), the machine never halts. -/
theorem not_halts_of_orbit (h : ∀ k, (orbit k .one 0).isSome = true) : ¬ HaltsFromBlank := by
  apply not_halts_of_forall
  intro n
  apply no_halt_of_orbit n (h n) n
  cases e : orbit n .one 0 with
  | none => have := h n; rw [e] at this; cases this
  | some p =>
    obtain ⟨T, m, t⟩ := p
    have := orbit_steps_ge n .one 0 T m t e
    simp only [orbitT, e]
    omega

/-- The E-event after `k` E-steps from blank tape (for printing). -/
def orbitE (k : Nat) : Option (Tail × Nat) := (orbit k .one 0).map (fun p => (p.1, p.2.1))

/-- The 37th E-event from blank tape is at step 20,999,239,576 (direct simulation agrees on all E-events up to
2.7·10⁹ steps). -/
theorem orbitT_37 : orbitT 37 = 20999239576 := by decide +kernel

/-- 3,000 E-steps from blank tape inside the map, evaluated by the kernel: no halt in the first `10^450` steps. -/
theorem orbit_3k : (orbit 3000 .one 0).isSome = true ∧ 10 ^ 450 < orbitT 3000 := by decide +kernel

theorem no_halt_3k : ∃ c, steps (10 ^ 450) init = some c :=
  no_halt_of_orbit 3000 orbit_3k.1 _ (Nat.le_of_lt orbit_3k.2)

/-- 100,000 E-steps from blank tape inside the map, by compiled evaluation: no halt in the first `10^16000`
steps. -/
theorem orbit_100k : (orbit 100000 .one 0).isSome = true ∧ 10 ^ 16000 < orbitT 100000 := by native_decide

theorem no_halt_100k : ∃ c, steps (10 ^ 16000) init = some c :=
  no_halt_of_orbit 100000 orbit_100k.1 _ (Nat.le_of_lt orbit_100k.2)

end H70770
