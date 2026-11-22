import Phase

/-!
# The level-1 orbit of 1RB0RE_0LC1LE_0RD1LD_1RA1LF_1LC0RA_0LB--- from blank tape, as a theorem

`next1` is the phase map of Phase.lean on the words D(a, b), R(a) and the length Z of the run of zeros; it is
`none` where Phase.lean proves nothing (R(a) with Z odd or Z ≡ 0 mod 4, R(0), Z too small).  `next1_sound`: each
step of it is a run of the machine, at least Z' steps long.  `iter1_sound` chains k of them.

From blank tape (`blank_start`, step 457) the first phase start is PS(D(2, 0), 15).  Evaluated by Lean's kernel
(`decide +kernel`, exact integers), the level-1 map runs 1001 phases from there: the counter resets at phases 5, 29,
92 and 332 stay in the family (Z ≡ 3 mod 8), and phase 1001 starts at PS(R(971), Z) with Z ≡ 0 mod 4 and 178
digits, where the word leaves the family.  So the machine does not halt in its first 10^177 steps (`blank_1001`).
Written by hand.
-/

namespace H53125

open TM

/-- The words of level 1. -/
inductive W1 where
  | d (a b : Nat)
  | r (a : Nat)
  deriving DecidableEq, Repr

def W1.tape : W1 → Tape
  | .d a b => Dw a b
  | .r a => Rw a

/-- One phase on (word, Z), where Phase.lean proves it. -/
def next1 : W1 × Nat → Option (W1 × Nat)
  | (.d a b, z) =>
    if z % 4 = 1 ∧ 9 ≤ z then some (.d a b, 3 * (z + 1) / 2)
    else if z % 4 = 3 ∧ 11 ≤ z then
      match a with
      | 0 => some (.r (3 * b + 5), 3 * (z + 1) / 2)
      | a + 1 => some (.d a (b + 1), 3 * (z - 1) / 2)
    else none
  | (.r a, z) =>
    if z % 4 = 2 ∧ 10 ≤ z then
      match a with
      | 0 => none
      | a + 1 => some (.d a 0, 3 * z / 2)
    else none

def cfg1 (x : W1 × Nat) : Config := PS x.1.tape x.2

theorem next1_sound (x y : W1 × Nat) (h : next1 x = some y) :
    ∃ s, y.2 ≤ s ∧ steps s (cfg1 x) = some (cfg1 y) := by
  obtain ⟨w, z⟩ := x
  cases w with
  | d a b =>
    simp only [next1] at h
    by_cases h1 : z % 4 = 1 ∧ 9 ≤ z
    · rw [if_pos h1] at h
      cases h
      obtain ⟨s, hs, hr⟩ := phase_D1 a b ((z - 9) / 4)
      have e1 : 4 * ((z - 9) / 4) + 9 = z := by omega
      have e2 : 6 * ((z - 9) / 4) + 15 = 3 * (z + 1) / 2 := by omega
      rw [e1, e2] at hr
      exact ⟨s, by show _ ≤ s; omega, hr⟩
    · rw [if_neg h1] at h
      by_cases h3 : z % 4 = 3 ∧ 11 ≤ z
      · rw [if_pos h3] at h
        have e1 : 4 * ((z - 11) / 4) + 11 = z := by omega
        cases a with
        | zero =>
          cases h
          obtain ⟨s, hs, hr⟩ := phase_D0 b ((z - 11) / 4)
          have e2 : 6 * ((z - 11) / 4) + 18 = 3 * (z + 1) / 2 := by omega
          rw [e1, e2] at hr
          exact ⟨s, by show _ ≤ s; omega, hr⟩
        | succ a =>
          cases h
          obtain ⟨s, hs, hr⟩ := phase_D3 a b ((z - 11) / 4)
          have e2 : 6 * ((z - 11) / 4) + 15 = 3 * (z - 1) / 2 := by omega
          rw [e1, e2] at hr
          exact ⟨s, by show _ ≤ s; omega, hr⟩
      · rw [if_neg h3] at h
        cases h
  | r a =>
    simp only [next1] at h
    by_cases h2 : z % 4 = 2 ∧ 10 ≤ z
    · rw [if_pos h2] at h
      cases a with
      | zero => cases h
      | succ a =>
        cases h
        obtain ⟨s, hs, hr⟩ := phase_R2 a ((z - 10) / 4)
        have e1 : 4 * ((z - 10) / 4) + 10 = z := by omega
        have e2 : 6 * ((z - 10) / 4) + 15 = 3 * z / 2 := by omega
        rw [e1, e2] at hr
        exact ⟨s, by show _ ≤ s; omega, hr⟩
    · rw [if_neg h2] at h
      cases h

/-- k phases of the level-1 map. -/
def iter1 : Nat → W1 × Nat → Option (W1 × Nat)
  | 0, x => some x
  | k + 1, x => (next1 x).bind (iter1 k)

theorem iter1_sound (k : Nat) (x y : W1 × Nat) (h : iter1 k x = some y) :
    ∃ s, y.2 ≤ s + x.2 ∧ steps s (cfg1 x) = some (cfg1 y) := by
  induction k generalizing x with
  | zero => cases h; exact ⟨0, by omega, rfl⟩
  | succ k ih =>
    unfold iter1 at h
    cases hx : next1 x with
    | none => rw [hx] at h; cases h
    | some x' =>
      rw [hx] at h
      obtain ⟨s1, hs1, h1⟩ := next1_sound x x' hx
      obtain ⟨s2, hs2, h2⟩ := ih x' h
      exact ⟨s1 + s2, by omega, steps_seq trans h1 h2⟩

/-- The first phase start from blank tape. -/
def x0 : W1 × Nat := (.d 2 0, 15)

theorem blank_x0 : steps 457 init = some (cfg1 x0) := by
  have h := blank_start
  simp only [cfg1, x0, W1.tape, PS, Dw, rep_succ, rep_zero, app_cons, app_nil]
  rw [cons_false_blank] at h
  exact h

/-- The level-1 map runs 1001 phases from `x0`, to Z > 10^177 (kernel evaluation, exact integers). -/
theorem iter1_1001 : (iter1 1001 x0).any (fun y => decide (10 ^ 177 ≤ y.2)) = true := by decide +kernel

/-- Phase 1001 has Z ≡ 0 mod 4 on a word R(a): the level-1 map stops there. -/
theorem iter1_1002 : iter1 1002 x0 = none := by decide +kernel

/-- No halt in the first 10^177 steps from blank tape. -/
theorem blank_1001 : ∃ s c, 10 ^ 177 ≤ s ∧ steps s init = some c := by
  cases hy : iter1 1001 x0 with
  | none => have h := iter1_1001; rw [hy] at h; cases h
  | some y =>
    have hb := iter1_1001
    rw [hy] at hb
    simp only [Option.any_some, decide_eq_true_eq] at hb
    obtain ⟨s, hs, h⟩ := iter1_sound 1001 x0 y hy
    exact ⟨457 + s, cfg1 y, by simp [x0] at hs; omega, steps_seq trans blank_x0 h⟩

end H53125
