import Collapse

/-!
# 1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---: the run from blank tape through the first rebuild

The run reaches the regular configuration `3 2 8 5 14 | 9` (in `enc` form) at step 2,918 (evaluated by the kernel on
the list simulator); from there `collapse` gives the first single block, 36 cells, after `T [4, 1, 2, 0] = 1,616`
sub-rounds, `rebuild` the sub-round after it, and `advance` 13 more, up to step 71,355, where the counter meets
a small gap (`first_uncovered`).  The kernel evaluates only the first 2,918 machine steps and the counter (`gstep`),
not the other 68,437 machine steps, which the rules of `Subround.lean` cover for all sizes.
-/

namespace H4320

open TM

theorem reach_2918 : steps 2918 init = some (enc 1 [4, 1, 2, 0] 9 []) := by
  have h := blank_reaches trans (n := 2918) (q := St.A) (by decide +kernel :
    fsteps 2918 (FCfg.blank St.A) = some ⟨[true, true, true, true, true, true, true, true, true, false, true, true,
      true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true,
      false, true, true, true, true, true, true, true, true, false, true, true, false, true, true, true], [], St.C⟩)
  refine h.trans ?_
  simp only [FCfg.toCfg, enc, zr, cons_false_blank, app_nil]
  rfl

theorem T_first : T [4, 1, 2, 0] = 1616 := by decide

theorem counter_first : giter 1616 (9, []) = some (9, [7, 7, 11, 3]) := by decide +kernel

/-- The first single block: 36 cells, last block 9, zone gaps 8 7 11 3, after 1,616 sub-rounds from step 2,918. -/
theorem first_single : ∃ n, steps n init = some (enc 12 [] 9 [7, 7, 11, 3]) := by
  obtain ⟨n, h⟩ := collapse 1616 1 [4, 1, 2, 0] (9, []) (9, [7, 7, 11, 3]) T_first counter_first
  exact ⟨2918 + n, steps_seq trans reach_2918 h⟩

/-- The sub-round after it: `3 2^11 | 5`, zone gaps 5 7 7 11 3 (step 70,871 of the run). -/
theorem first_rebuild : ∃ n, steps n init = some (enc 1 (List.replicate 11 0) 5 [4, 7, 7, 11, 3]) := by
  obtain ⟨n₁, h₁⟩ := first_single
  obtain ⟨n₂, h₂⟩ := rebuild 11 4 [7, 7, 11, 3]
  exact ⟨n₁ + n₂, steps_seq trans h₁ h₂⟩

/-- Thirteen sub-rounds later (step 71,355 of the run) the counter's carry meets a gap of 2 cells, which the rules
here do not cover: `3 2^6 8 5 | 1`, zone gaps 4 3 2 5 7 11 3.  The run up to there is proved. -/
theorem first_uncovered :
    (∃ n, steps n init = some (enc 1 [1, 2, 0, 0, 0, 0, 0, 0] 1 [3, 3, 2, 5, 7, 11, 3])) ∧
      gstep (1, [3, 3, 2, 5, 7, 11, 3]) = none := by
  refine ⟨?_, by decide⟩
  obtain ⟨n₁, h₁⟩ := first_rebuild
  obtain ⟨n₂, h₂⟩ := advance 13 1 (List.replicate 11 0) (5, [4, 7, 7, 11, 3]) (1, [3, 3, 2, 5, 7, 11, 3])
    (by decide) (by decide +kernel)
  exact ⟨n₁ + n₂, steps_seq trans h₁ h₂⟩

end H4320
