import Macro

/-!
# The machine halts iff the orbit of `next` from `Z 1` reaches `Z k` with `k` even

`orbit n` is the n-th round start from blank tape (`none` once a round has halted).  From blank tape the machine
reaches `Z 1` in 10 steps (`blank_start`); `round` and `round_halt` (Macro.lean) do the rest.  Checked by Lean's kernel;
the proof of `halts_iff` uses `Classical.byContradiction`.
-/

namespace H174634

open TM

/-- The round starts from blank tape. -/
def orbit : Nat → Option S2
  | 0 => some (.z 1)
  | n + 1 => (orbit n).bind next

theorem start_blank : steps 10 init = some (enc (.z 1)) := blank_start

/-- Every round start on the orbit is reached from blank tape, after at least `n` steps. -/
theorem orbit_reached : ∀ n s, orbit n = some s → ∃ m, n ≤ m ∧ steps m init = some (enc s) := by
  intro n
  induction n with
  | zero =>
    intro s h
    cases h
    exact ⟨10, by omega, start_blank⟩
  | succ n ih =>
    intro s h
    simp only [orbit] at h
    cases ho : orbit n with
    | none => rw [ho] at h; cases h
    | some t =>
      rw [ho] at h
      obtain ⟨m, hm, hr⟩ := ih _ ho
      obtain ⟨j, hj⟩ := round (s := t) h
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
      obtain ⟨m, _, hr⟩ := orbit_reached n _ ho
      obtain ⟨j, d, hj, hd⟩ := round_halt (s := t) h
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
    obtain ⟨m, hm, hr⟩ := orbit_reached n s hs
    exact ⟨m, hm, _, hr⟩
  · rintro ⟨n, h⟩
    exact halts_of_orbit_none n h

/-- The same, with the halting condition written out: the machine halts iff the orbit reaches `Z k` with `k`
even. -/
theorem halts_iff' : HaltsFromBlank ↔ ∃ n k, orbit n = some (.z k) ∧ k % 2 = 0 := by
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
        change next t = none at h
        cases t with
        | r a b =>
          simp only [next] at h
          split at h
          · cases h
          · split at h <;> cases h
        | z k =>
          refine ⟨n, k, ho, ?_⟩
          simp only [next] at h
          split at h
          · assumption
          · cases h
  · rintro ⟨n, k, h, hk⟩
    refine ⟨n + 1, ?_⟩
    simp only [orbit, h, Option.bind]
    simp only [next, if_pos hk]

/-! ## The first rounds, by the kernel -/

/-- `true` iff `n` rounds from `s` do not halt. -/
def safe : Nat → S2 → Bool
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

/-- The first 10,000 rounds do not halt (`n` then has about 5,800 bits). -/
theorem first_rounds : ∀ i, i ≤ 10000 → orbit i ≠ none := by
  intro i hi
  have := safe_orbit 10000 0 (.z 1) rfl (by decide +kernel) i hi
  simpa using this

end H174634
