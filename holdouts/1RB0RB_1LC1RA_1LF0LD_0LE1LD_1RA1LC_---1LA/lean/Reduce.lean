import Sweep

/-!
# 1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA: halting is a question about the pass orbit

* `orbT k`: the k-th turn configuration of the run from blank tape, as `(out, rest, t)` with `t` the step count
  (`none` once a macro step has halted); `orbT_sound`: it is a run of the machine.
* **`halts_iff`: the machine halts from blank tape if and only if some macro step of the orbit halts.**

So the macro machine `mstep` of `Sweep.lean` is an exact reduction.  Everything is checked by Lean's kernel.
-/

namespace H73071

open TM

/-- The orbit of turn configurations with their step counts. -/
def orbT : Nat → Option (List Bool × List Bool × Nat)
  | 0 => some ([], [], 2)
  | k + 1 =>
    match orbT k with
    | none => none
    | some (o, r, t) =>
      match mstep o r with
      | .go n o' r' => some (o', r', t + n)
      | .halt _ => none

theorem orbT_sound : ∀ (k : Nat) (o r : List Bool) (t : Nat), orbT k = some (o, r, t) →
    steps t init = some (RT o r) ∧ k ≤ t
  | 0, o, r, t, h => by
    simp only [orbT, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨init_RT, by omega⟩
  | k + 1, o, r, t, h => by
    simp only [orbT] at h
    cases hp : orbT k with
    | none => rw [hp] at h; cases h
    | some p =>
      obtain ⟨o0, r0, t0⟩ := p
      rw [hp] at h
      simp only at h
      cases hm : mstep o0 r0 with
      | halt _ => rw [hm] at h; cases h
      | go n o1 r1 =>
        rw [hm] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨ht, hk⟩ := orbT_sound k o0 r0 t0 hp
        have hs := mstep_sound o0 r0
        rw [hm] at hs
        exact ⟨steps_seq trans ht hs, by have := mstep_pos hm; omega⟩

/-- The orbit halts at macro step `k`. -/
def HaltsAt (k : Nat) : Prop := ∃ o r t n, orbT k = some (o, r, t) ∧ mstep o r = .halt n

theorem halts_of_orbit {k : Nat} (h : HaltsAt k) : HaltsFromBlank := by
  obtain ⟨o, r, t, n, h1, h2⟩ := h
  have ht := (orbT_sound k o r t h1).1
  have hs := mstep_sound o r
  rw [h2] at hs
  obtain ⟨c', h3, h4⟩ := hs
  exact ⟨t + n, c', steps_seq trans ht h3, h4⟩

theorem orbT_some (hN : ∀ k, ¬ HaltsAt k) : ∀ k, ∃ o r t, orbT k = some (o, r, t)
  | 0 => ⟨[], [], 2, rfl⟩
  | k + 1 => by
    obtain ⟨o, r, t, h⟩ := orbT_some hN k
    cases hm : mstep o r with
    | halt n => exact absurd ⟨o, r, t, n, h, hm⟩ (hN k)
    | go n o' r' => exact ⟨o', r', t + n, by simp only [orbT, h, hm]⟩

/-- **The reduction.** The machine halts from blank tape iff the pass orbit halts. -/
theorem halts_iff : HaltsFromBlank ↔ ∃ k, HaltsAt k := by
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hN
    have hN' : ∀ k, ¬ HaltsAt k := fun k hk => hN ⟨k, hk⟩
    refine not_halts_of_forall trans (forall_of_unbounded trans (fun m => ∃ c, steps m init = some c) ?_ ?_) hH
    · intro n
      obtain ⟨o, r, t, h⟩ := orbT_some hN' n
      obtain ⟨ht, hk⟩ := orbT_sound n o r t h
      exact ⟨t, hk, _, ht⟩
    · intro m hm; exact hm
  · rintro ⟨k, hk⟩
    exact halts_of_orbit hk

end H73071
