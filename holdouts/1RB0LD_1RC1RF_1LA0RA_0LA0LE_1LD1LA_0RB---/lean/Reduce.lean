import Macro
set_option linter.unusedSimpArgs false

/-!
# 1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---: halting is a question about the orbit of (z, y)

* `next z y`: one macro step, `z = 3k + r`:
  `(3k, y) ↦ (4k+1, y+4)`, `(3k+1, y) ↦ (4k+5, y+6)`, `(3k+2, y) ↦ (4k+8, y-1)`, the last two only for `y ≥ 1`
  (`none` otherwise: the rules stop applying).  `next_sound`: the machine follows it, in `mcost z y` steps.
* `init_wall`: blank tape reaches the wall `C 0 0` after 7 steps.
* `orb n`: the n-th macro configuration from `(0, 0)`.
* **`not_halts_of_orbit`: if the orbit never leaves the rules (never has `y = 0` with `z % 3 ≠ 0`), the machine
  never halts from blank tape.**  `orb_exit`: leaving the rules happens only that way.

Everything is checked by Lean's kernel.
-/

namespace H141950

open TM

/-- One macro step on `(z, y)`. -/
def next (z y : Nat) : Option (Nat × Nat) :=
  if z % 3 = 0 then some (4 * (z / 3) + 1, y + 4)
  else if y = 0 then none
  else if z % 3 = 1 then some (4 * (z / 3) + 5, y + 6)
  else some (4 * (z / 3) + 8, y - 1)

/-- Its cost in machine steps. -/
def mcost (z y : Nat) : Nat :=
  (4 * ((z / 3) * (z / 3)) + 7 * (z / 3)) +
    (if z % 3 = 0 then 4 * (2 * (z / 3)) + 8 * y + 37
     else if z % 3 = 1 then 8 * (2 * (z / 3)) + 16 * (y - 1) + 110
     else 8 * (2 * (z / 3)) + 28)

theorem next_sound {z y z' y' : Nat} (h : next z y = some (z', y')) :
    steps (mcost z y) (C z y) = some (C z' y') := by
  have hz : z = z % 3 + 3 * (z / 3) := by omega
  have hs := sweeps (z / 3) 0 (z % 3) (tl y)
  have hc := scost_eq 0 (z / 3)
  rw [show scost 0 (z / 3) = 4 * ((z / 3) * (z / 3)) + 7 * (z / 3) by omega] at hs
  rw [← hz, Nat.zero_add] at hs
  unfold next at h
  unfold mcost
  split at h
  · rename_i h0
    cases h
    simp only [h0, ↓reduceIte]
    have he := end0 (2 * (z / 3)) y
    rw [show 2 * (2 * (z / 3)) + 1 = 4 * (z / 3) + 1 by omega] at he
    rw [h0] at hs
    exact steps_seq trans hs he
  · rename_i h0
    split at h
    · cases h
    · rename_i hy
      obtain ⟨y1, rfl⟩ : ∃ y1, y = y1 + 1 := ⟨y - 1, by omega⟩
      split at h
      · rename_i h1
        cases h
        simp only [h0, h1, ↓reduceIte]
        have he := end1 (2 * (z / 3)) y1
        rw [show 2 * (2 * (z / 3)) + 5 = 4 * (z / 3) + 5 by omega] at he
        rw [h1] at hs
        rw [show y1 + 1 + 6 = y1 + 7 by omega, show y1 + 1 - 1 = y1 by omega]
        exact steps_seq trans hs he
      · rename_i h1
        cases h
        simp only [h0, h1, ↓reduceIte]
        have he := end2 (2 * (z / 3)) y1
        rw [show 2 * (2 * (z / 3)) + 8 = 4 * (z / 3) + 8 by omega] at he
        rw [show z % 3 = 2 by omega] at hs
        rw [show y1 + 1 - 1 = y1 by omega]
        exact steps_seq trans hs he

theorem mcost_pos (z y : Nat) : 1 ≤ mcost z y := by
  unfold mcost; split
  · omega
  · split <;> omega

theorem init_wall : steps 7 init = some (C 0 0) := by
  have h : steps 7 init = some ⟨blank, cons false (cons false (cons true (cons false (cons false (cons true
      blank))))), .A⟩ := rfl
  rw [h]; rfl

/-- The macro orbit from the first wall `(0, 0)`. -/
def orb : Nat → Option (Nat × Nat)
  | 0 => some (0, 0)
  | n + 1 => (orb n).bind (fun p => next p.1 p.2)

/-- Leaving the rules happens only at `y = 0` with `z` not a multiple of 3. -/
theorem next_none {z y : Nat} (h : next z y = none) : y = 0 ∧ z % 3 ≠ 0 := by
  unfold next at h
  split at h
  · cases h
  · split at h
    · rename_i h0 hy; exact ⟨hy, h0⟩
    · split at h <;> cases h

theorem orb_exit {n z y : Nat} (h : orb n = some (z, y)) (h' : orb (n + 1) = none) : y = 0 ∧ z % 3 ≠ 0 := by
  simp only [orb, h, Option.bind_some] at h'
  exact next_none h'

theorem reach_orb (hN : ∀ n, orb n ≠ none) : ∀ n, ∃ t z y, n ≤ t ∧ steps t init = some (C z y) ∧
    orb n = some (z, y)
  | 0 => ⟨7, 0, 0, by omega, init_wall, rfl⟩
  | n + 1 => by
    obtain ⟨t, z, y, hn, ht, ho⟩ := reach_orb hN n
    have h1 := hN (n + 1)
    simp only [orb, ho, Option.bind_some] at h1 ⊢
    cases hx : next z y with
    | none => exact absurd hx h1
    | some p =>
      obtain ⟨z', y'⟩ := p
      exact ⟨t + mcost z y, z', y', by have := mcost_pos z y; omega,
        steps_seq trans ht (next_sound hx), rfl⟩

/-- **The reduction.**  If the macro orbit never leaves the rules, the machine never halts from blank tape. -/
theorem not_halts_of_orbit (hN : ∀ n, orb n ≠ none) : ¬ HaltsFromBlank := by
  refine not_halts_of_forall trans (forall_of_unbounded trans (fun m => ∃ c, steps m init = some c) ?_ ?_)
  · intro n
    obtain ⟨t, z, y, hn, ht, _⟩ := reach_orb hN n
    exact ⟨t, hn, _, ht⟩
  · intro m hm; exact hm

end H141950
