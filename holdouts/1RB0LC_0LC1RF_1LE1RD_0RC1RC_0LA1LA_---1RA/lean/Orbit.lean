import Map

/-!
# The run from blank tape, event by event

`init_U`: the run from blank tape is at the event `Ev .U 4 3` after 118 steps.  `orbit k F a b` applies the map
`next` (proved in `Map.lean`) `k` times from `Ev F a b` and returns where it is and how many steps it took, or
`none` if the map is undefined on the way (a halting event, or odd a).  `orbit_sound` turns a value of `orbit` into
a statement about the machine; the theorems at the end evaluate it, in the kernel and with `native_decide`.
-/

namespace H13743

open TM

theorem init_U : steps 118 init = some (Ev .U 4 3) :=
  blank_reaches trans (q := St.A) (n := 118)
    (c := ⟨[], [false, true, true, false, true, true, true, true, true, true, false, true, true, true], .A⟩)
    (by decide +kernel)

/-- `k` events on from `Ev F a b`: the end and the number of steps, or `none` if the map is undefined on the way. -/
def orbit : Nat → Tag → Nat → Nat → Option (Tag × Nat × Nat × Nat)
  | 0, F, a, b => some (F, a, b, 0)
  | k + 1, F, a, b =>
    match next F a b with
    | some (F', a', b', s) => (orbit k F' a' b').map (fun p => (p.1, p.2.1, p.2.2.1, s + p.2.2.2))
    | none => none

theorem orbit_sound : ∀ k F a b F' a' b' t, orbit k F a b = some (F', a', b', t) →
    steps t (Ev F a b) = some (Ev F' a' b') := by
  intro k
  induction k with
  | zero => intro F a b F' a' b' t h; simp [orbit] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; rfl
  | succ k ih =>
    intro F a b F' a' b' t h
    unfold orbit at h
    cases e : next F a b with
    | none => rw [e] at h; cases h
    | some q =>
      obtain ⟨F₁, a₁, b₁, s⟩ := q
      rw [e] at h
      dsimp only at h
      cases e2 : orbit k F₁ a₁ b₁ with
      | none => rw [e2] at h; cases h
      | some p =>
        rw [e2] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨F₂, a₂, b₂, t₂⟩ := p
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact steps_seq trans (next_sound F a b (F₁, a₁, b₁, s) e) (ih F₁ a₁ b₁ F₂ a₂ b₂ t₂ e2)

/-- The number of steps to the `k`-th event after `U(4, 3)` from blank tape (0 if the map is undefined on the way). -/
def orbitT (k : Nat) : Nat := match orbit k .U 4 3 with | some p => 118 + p.2.2.2 | none => 0

/-- No halt in the first `n ≤ orbitT k` steps when the first `k` events after `U(4, 3)` are covered by the map. -/
theorem no_halt_of_orbit (k : Nat) (h : (orbit k .U 4 3).isSome = true) (n : Nat) (hn : n ≤ orbitT k) :
    ∃ c, steps n init = some c := by
  cases e : orbit k .U 4 3 with
  | none => rw [e] at h; cases h
  | some p =>
    obtain ⟨F, a, b, t⟩ := p
    have hr := steps_seq trans init_U (orbit_sound k .U 4 3 F a b t e)
    simp only [orbitT, e] at hn
    exact steps_le trans (show steps (n + (118 + t - n)) init = _ by rw [show n + (118 + t - n) = 118 + t by omega]; exact hr)

theorem orbit_steps_ge : ∀ k F a b F' a' b' t, orbit k F a b = some (F', a', b', t) → k ≤ t := by
  intro k
  induction k with
  | zero => intro F a b F' a' b' t _; exact Nat.zero_le _
  | succ k ih =>
    intro F a b F' a' b' t h
    unfold orbit at h
    cases e : next F a b with
    | none => rw [e] at h; cases h
    | some q =>
      obtain ⟨F₁, a₁, b₁, s⟩ := q
      rw [e] at h
      dsimp only at h
      cases e2 : orbit k F₁ a₁ b₁ with
      | none => rw [e2] at h; cases h
      | some p =>
        rw [e2] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨F₂, a₂, b₂, t₂⟩ := p
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        have h1 := next_pos F a b (F₁, a₁, b₁, s) e
        have h2 := ih F₁ a₁ b₁ F₂ a₂ b₂ t₂ e2
        simp only at h1
        omega

/-- **Non-halting reduces to the map.** If the orbit of `next` from `U(4, 3)` never gets stuck (by `next_isSome`:
never reaches a halting event `a = 0 mod 4, b = 1`, an odd `a`, or `b = 0`), the machine never halts. -/
theorem not_halts_of_orbit (h : ∀ k, (orbit k .U 4 3).isSome = true) : ¬ HaltsFromBlank := by
  apply not_halts_of_forall
  intro n
  apply no_halt_of_orbit n (h n) n
  cases e : orbit n .U 4 3 with
  | none => have := h n; rw [e] at this; cases this
  | some p =>
    obtain ⟨F, a, b, t⟩ := p
    have := orbit_steps_ge n .U 4 3 F a b t e
    simp only [orbitT, e]
    omega

/-- The event after `k` events from `U(4, 3)` (for printing). -/
def orbitE (k : Nat) : Option (Tag × Nat × Nat) := (orbit k .U 4 3).map (fun p => (p.1, p.2.1, p.2.2.1))

/-- 3,000 events from blank tape inside the map, evaluated by the kernel: no halt in the first `orbitT 3000`
steps, which is more than `10^500`. -/
theorem orbit_3k : (orbit 3000 .U 4 3).isSome = true ∧ 10 ^ 500 < orbitT 3000 := by decide +kernel

theorem no_halt_3k : ∃ c, steps (10 ^ 500) init = some c :=
  no_halt_of_orbit 3000 orbit_3k.1 _ (Nat.le_of_lt orbit_3k.2)

/-- The 34th event after `U(4, 3)` is `U(35354, 10986)` at step 1,916,511,832, as direct simulation finds. -/
theorem orbit_34 : orbitE 34 = some (.U, 35354, 10986) ∧ orbitT 34 = 1916511832 := by decide +kernel

/-- 100,000 events from blank tape inside the map, by compiled evaluation: no halt in the first `10^10000` steps. -/
theorem orbit_100k : (orbit 100000 .U 4 3).isSome = true ∧ 10 ^ 10000 < orbitT 100000 := by native_decide

theorem no_halt_100k : ∃ c, steps (10 ^ 10000) init = some c :=
  no_halt_of_orbit 100000 orbit_100k.1 _ (Nat.le_of_lt orbit_100k.2)

end H13743
