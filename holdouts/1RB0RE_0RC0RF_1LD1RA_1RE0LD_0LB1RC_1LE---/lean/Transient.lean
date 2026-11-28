import General
import Run

/-!
# 1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---: the run from blank tape through the third single block

`Run.lean` proves the run up to step 71,355, the first sub-round with a small gap.  The pass machine of
`General.lean` covers every sub-round, so from there the kernel evaluates the sub-rounds of the first transient
(`sub`, 7 of them) up to a regular configuration, `collapse` (with the counter `giter` evaluated by the kernel,
260,270 steps of it) gives the second single block (57 cells), `rebuild` the sub-round after it, the pass machine
the 24 sub-rounds of the second transient, and `collapse_regular` the third single block (90 cells) more than
2^29 sub-rounds later, with a regular counter.  No step of the machine is evaluated here: the kernel evaluates only
the pass machine and the counter.
-/

namespace H4320

open TM

/-- The digits after the first transient: `3 2^6 11 5^2 2^2 5` (nearest last). -/
def D1 : List Nat := [1, 0, 0, 1, 1, 3, 0, 0, 0, 0, 0, 0]

/-- The first transient: 7 sub-rounds of the pass machine from step 71,355, to the regular configuration
`3 2^6 11 5^2 2^2 5 | 5`, zone gaps 4 7 3 (step 71,680). -/
theorem first_transient : ∃ n, steps n init = some (enc 1 D1 5 [3, 7, 3]) := by
  obtain ⟨n₁, h₁⟩ := first_uncovered.1
  have h₂ := subs_moment 100 7 (encBlocks 1 [1, 2, 0, 0, 0, 0, 0, 0]) 1 [3, 3, 2, 5, 7, 11, 3]
    (encBlocks 1 D1) 5 [3, 7, 3] 325 (by decide +kernel)
  rw [enc_gcfg] at h₁
  rw [enc_gcfg]
  exact ⟨n₁ + 325, steps_seq trans h₁ h₂⟩

theorem T_D1 : T D1 = 260270 := by decide

theorem counter_second : giter 260270 (5, [3, 7, 3]) = some (9, [11, 3, 3, 15, 3, 3, 3, 3, 3, 3]) := by
  decide +kernel

/-- The second single block: 57 cells, last block 9, zone gaps 12 3 3 15 3 3 3 3 3 3. -/
theorem second_single : ∃ n, steps n init = some (enc 19 [] 9 [11, 3, 3, 15, 3, 3, 3, 3, 3, 3]) := by
  obtain ⟨n₁, h₁⟩ := first_transient
  obtain ⟨n₂, h₂⟩ := collapse 260270 1 D1 (5, [3, 7, 3]) _ T_D1 counter_second
  exact ⟨n₁ + n₂, steps_seq trans h₁ h₂⟩

/-- The digits after the second transient: `3 2^13 11 5^2 2^2 5 2^2 5` (nearest last). -/
def D2 : List Nat := [1, 0, 0, 1, 0, 0, 1, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The second rebuild (`3 2^18 | 5`, a new gap of 4) and its transient, 24 sub-rounds of the pass machine, to the
regular configuration `3 2^13 11 5^2 2^2 5 2^2 5 | 9` with zone gaps 4 3 3 3 3 3 3. -/
theorem second_transient : ∃ n, steps n init = some (enc 1 D2 9 [3, 3, 3, 3, 3, 3, 3]) := by
  obtain ⟨n₁, h₁⟩ := second_single
  obtain ⟨n₂, h₂⟩ := rebuild 18 4 [11, 3, 3, 15, 3, 3, 3, 3, 3, 3]
  have h₃ := subs_moment 100 24 (encBlocks 1 (List.replicate 18 0)) 5 [4, 11, 3, 3, 15, 3, 3, 3, 3, 3, 3]
    (encBlocks 1 D2) 9 [3, 3, 3, 3, 3, 3, 3] 1015 (by decide +kernel)
  rw [enc_gcfg 1 (List.replicate 18 0)] at h₂
  rw [enc_gcfg]
  exact ⟨n₁ + n₂ + 1015, steps_seq trans (steps_seq trans h₁ h₂) h₃⟩

theorem mass_D2 : mass 1 D2 = 30 := by decide

/-- **The third single block** (90 cells, more than 2^29 sub-rounds after the second): the run from blank tape
reaches it with a regular counter, so without a halt before it. -/
theorem third_single : ∃ y n, Reg y ∧ steps n init = some (enc 30 [] y.1 y.2) := by
  obtain ⟨n₁, h₁⟩ := second_transient
  obtain ⟨y, n₂, hy, h₂⟩ := collapse_regular 1 D2 (9, [3, 3, 3, 3, 3, 3, 3])
    ⟨by decide, by decide⟩
  rw [mass_D2] at h₂
  exact ⟨y, n₁ + n₂, hy, steps_seq trans h₁ h₂⟩

theorem T_D2 : T D2 = 536840942 := by decide

end H4320
