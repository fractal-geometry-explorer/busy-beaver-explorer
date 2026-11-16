import Sweep

/-!
# 1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA: halting is a question about the macro orbit

* `orbT k`: the k-th state of the macro machine on the run from blank tape, with the step count `t` (`none` once a
  macro step has halted); `orbT_sound`: it is a run of the machine.
* **`halts_iff`: the machine halts from blank tape if and only if some macro step of the orbit halts.**

So the macro machine `mstep` of `Sweep.lean` is an exact reduction.  Everything is checked by Lean's kernel.
-/

namespace H25821

open TM

/-- The orbit of the macro machine with the step counts. -/
def orbT : Nat → Option (MS × Nat)
  | 0 => some (.rt [], 3)
  | k + 1 =>
    match orbT k with
    | none => none
    | some (s, t) =>
      match mstep s with
      | .go n s' => some (s', t + n)
      | .halt _ => none

theorem orbT_sound : ∀ (k : Nat) (s : MS) (t : Nat), orbT k = some (s, t) → steps t init = some s.cfg ∧ k ≤ t
  | 0, s, t, h => by
    simp only [orbT, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨init_RT, by omega⟩
  | k + 1, s, t, h => by
    simp only [orbT] at h
    cases hp : orbT k with
    | none => rw [hp] at h; cases h
    | some p =>
      obtain ⟨s0, t0⟩ := p
      rw [hp] at h
      simp only at h
      cases hm : mstep s0 with
      | halt _ => rw [hm] at h; cases h
      | go n s1 =>
        rw [hm] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ht, hk⟩ := orbT_sound k s0 t0 hp
        have hs := mstep_sound s0
        rw [hm] at hs
        exact ⟨steps_seq trans ht hs, by have := mstep_pos hm; omega⟩

/-- The orbit halts at macro step `k`. -/
def HaltsAt (k : Nat) : Prop := ∃ s t n, orbT k = some (s, t) ∧ mstep s = .halt n

theorem halts_of_orbit {k : Nat} (h : HaltsAt k) : HaltsFromBlank := by
  obtain ⟨s, t, n, h1, h2⟩ := h
  have ht := (orbT_sound k s t h1).1
  have hs := mstep_sound s
  rw [h2] at hs
  obtain ⟨c', h3, h4⟩ := hs
  exact ⟨t + n, c', steps_seq trans ht h3, h4⟩

theorem orbT_some (hN : ∀ k, ¬ HaltsAt k) : ∀ k, ∃ s t, orbT k = some (s, t)
  | 0 => ⟨.rt [], 3, rfl⟩
  | k + 1 => by
    obtain ⟨s, t, h⟩ := orbT_some hN k
    cases hm : mstep s with
    | halt n => exact absurd ⟨s, t, n, h, hm⟩ (hN k)
    | go n s' => exact ⟨s', t + n, by simp only [orbT, h, hm]⟩

/-- **The reduction.** The machine halts from blank tape iff the macro orbit halts. -/
theorem halts_iff : HaltsFromBlank ↔ ∃ k, HaltsAt k := by
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hN
    have hN' : ∀ k, ¬ HaltsAt k := fun k hk => hN ⟨k, hk⟩
    refine not_halts_of_forall trans (forall_of_unbounded trans (fun m => ∃ c, steps m init = some c) ?_ ?_) hH
    · intro n
      obtain ⟨s, t, h⟩ := orbT_some hN' n
      obtain ⟨ht, hk⟩ := orbT_sound n s t h
      exact ⟨t, hk, _, ht⟩
    · intro m hm; exact hm
  · rintro ⟨k, hk⟩
    exact halts_of_orbit hk

end H25821
