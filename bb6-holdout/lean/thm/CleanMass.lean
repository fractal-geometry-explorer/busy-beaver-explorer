import CleanTheorem
open BB6 BB6.Sym

/-! # The cut classes of the 36-digit clean-tape tree

`clean_tree_step` and the end-to-end theorems hold at every depth with nothing evaluated; this file evaluates how much
the 36-digit tree leaves open: the leaf counts and the cut measure of `cleanTree 36`, computed by `exploreMassW` (the
same exploration, without building the tree) with `native_decide`.  No theorem about the machine uses them. -/

theorem clean_mass_36 :
    exploreMassW cleanGamma 1000 (10000 + 36) 36 36 false ctStart.1 ctStart.2.1 ctStart.2.1 ctStart.2.2 =
      (1660086, 1660017, 1507364) := by
  native_decide

/-- The cut classes of the 36-digit clean-tape tree have measure 1,660,086 / 2^36 ≈ 2.4 × 10⁻⁵ of the clean tapes of
width ≥ 2³²: 1,660,017 cut leaves (7 of them above depth 36, where a comparison is decided for every member of the
class but its smallest) and 1,507,364 closed ones. -/
theorem clean_tree_cut_mass : (cleanTree 36).cutMass 36 = 1660086 ∧ (cleanTree 36).leaves = (1660017, 1507364) := by
  have h := exploreMassW_eq cleanGamma 1000 (10000 + 36) 36 36 false ctStart.1 ctStart.2.1 ctStart.2.1 ctStart.2.2
  rw [clean_mass_36, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩
