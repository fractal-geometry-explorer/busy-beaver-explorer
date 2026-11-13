import Macro

/-!
# The machine halts iff the orbit of `next` from (P, 3, 0) meets `u = v` or `u = v + 1`

`orbit n` is the n-th round start from blank tape (`none` once a round has halted).  From blank tape the machine
reaches `P 3 0` in 42 steps (`blank_start`); `round` and `round_halt` (Macro.lean) do the rest.  Checked by Lean's
kernel; the proof of `halts_iff` uses `Classical.byContradiction`.
-/

namespace H151747

open TM

/-- The round starts from blank tape, as counts. -/
def orbit : Nat → Option (K × Nat × Nat)
  | 0 => some (.p, 3, 0)
  | n + 1 => (orbit n).bind next

theorem next_three {k : K} {u v : Nat} {s : K × Nat × Nat} (hu : 3 ≤ u) (h : next (k, u, v) = some s) :
    3 ≤ s.2.1 := by
  simp only [next] at h
  split at h
  · cases h
  · split at h <;> (cases h; dsimp only; split <;> omega)

theorem start_blank : steps 42 init = some (enc .p 3 0) := by
  have h := blank_start
  simp only [enc, rep_succ, rep_zero, app_cons, app_nil, cons_false_blank]
  exact h

/-- Every round start on the orbit is reached from blank tape, after at least `n` steps, and has `u ≥ 3`. -/
theorem orbit_reached : ∀ n s, orbit n = some s →
    3 ≤ s.2.1 ∧ ∃ m, n ≤ m ∧ steps m init = some (enc s.1 s.2.1 s.2.2) := by
  intro n
  induction n with
  | zero =>
    intro s h
    cases h
    exact ⟨by decide, 42, by omega, start_blank⟩
  | succ n ih =>
    intro s h
    simp only [orbit] at h
    cases ho : orbit n with
    | none => rw [ho] at h; cases h
    | some t =>
      rw [ho] at h
      obtain ⟨k, u, v⟩ := t
      obtain ⟨hu, m, hm, hr⟩ := ih _ ho
      obtain ⟨k', u', v'⟩ := s
      have hn : next (k, u, v) = some (k', u', v') := h
      refine ⟨next_three hu hn, ?_⟩
      obtain ⟨j, hj⟩ := round k u v hu hn
      exact ⟨m + (j + 1), by omega, steps_seq trans hr hj⟩

theorem halts_of_orbit_none : ∀ n, orbit n = none → HaltsFromBlank := by
  intro n
  induction n with
  | zero => intro h; cases h
  | succ n ih =>
    intro h
    simp only [orbit] at h
    cases ho : orbit n with
    | none => exact ih ho
    | some t =>
      rw [ho] at h
      obtain ⟨k, u, v⟩ := t
      obtain ⟨hu, m, _, hr⟩ := orbit_reached n _ ho
      obtain ⟨j, d, hj, hd⟩ := round_halt k u v hu h
      exact ⟨m + j, d, steps_seq trans hr hj, hd⟩

/-- **The machine halts from blank tape iff some round of the orbit halts.** -/
theorem halts_iff : HaltsFromBlank ↔ ∃ n, orbit n = none := by
  constructor
  · intro hh
    refine Classical.byContradiction fun hn => ?_
    have all : ∀ n, ∃ s, orbit n = some s := by
      intro n
      cases h : orbit n with
      | none => exact absurd ⟨n, h⟩ hn
      | some s => exact ⟨s, rfl⟩
    apply not_halts_of_forall trans (c := init) _ hh
    refine forall_of_unbounded trans (fun m => ∃ c, steps m init = some c) ?_ (fun _ h => h)
    intro n
    obtain ⟨s, hs⟩ := all n
    obtain ⟨_, m, hm, hr⟩ := orbit_reached n s hs
    exact ⟨m, hm, _, hr⟩
  · rintro ⟨n, h⟩
    exact halts_of_orbit_none n h

/-- The same, with the halting condition written out: the machine halts iff the orbit reaches a pair with
`u = v` or `u = v + 1`. -/
theorem halts_iff' : HaltsFromBlank ↔ ∃ n k u v, orbit n = some (k, u, v) ∧ (u = v ∨ u = v + 1) := by
  rw [halts_iff]
  constructor
  · rintro ⟨n, h⟩
    induction n with
    | zero => cases h
    | succ n ih =>
      simp only [orbit] at h
      cases ho : orbit n with
      | none => exact ih ho
      | some t =>
        rw [ho] at h
        obtain ⟨k, u, v⟩ := t
        refine ⟨n, k, u, v, ho, ?_⟩
        change next (k, u, v) = none at h
        simp only [next] at h
        split at h
        · assumption
        · split at h <;> cases h
  · rintro ⟨n, k, u, v, h, hc⟩
    refine ⟨n + 1, ?_⟩
    simp only [orbit, h, Option.bind]
    simp only [next, if_pos hc]

/-! ## The first rounds, by the kernel -/

/-- `true` iff `n` rounds from `s` do not halt. -/
def safe : Nat → K × Nat × Nat → Bool
  | 0, _ => true
  | n + 1, s =>
    match next s with
    | none => false
    | some s' => safe n s'

theorem safe_orbit (N : Nat) : ∀ n s, orbit n = some s → safe N s = true → ∀ i, i ≤ N → orbit (n + i) ≠ none := by
  induction N with
  | zero =>
    intro n s h _ i hi
    obtain rfl : i = 0 := by omega
    simp [h]
  | succ N ih =>
    intro n s h hs i hi
    cases i with
    | zero => simp [h]
    | succ i =>
      simp only [safe] at hs
      cases hn : next s with
      | none => rw [hn] at hs; cases hs
      | some s' =>
        rw [hn] at hs
        have h' : orbit (n + 1) = some s' := by simp only [orbit, h, Option.bind, hn]
        rw [show n + (i + 1) = n + 1 + i by omega]
        exact ih (n + 1) s' h' hs i (by omega)

/-- The first 10,000 rounds do not halt (the counts reach about 3,000 bits). -/
theorem first_rounds : ∀ i, i ≤ 10000 → orbit i ≠ none := by
  intro i hi
  have := safe_orbit 10000 0 (.p, 3, 0) rfl (by decide +kernel) i hi
  simpa using this

end H151747
