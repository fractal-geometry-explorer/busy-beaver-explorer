import CleanTheorem
open BB6 BB6.Sym

/-! # The cut classes of the 40-digit clean-tape tree

As `thm/CleanMass.lean`, at 40 digits: the leaf counts and the cut measure of `cleanTree 40`, computed by
`exploreMassW` with `native_decide` (about half an hour of native code).  No theorem about the machine uses them. -/

theorem clean_mass_40 :
    exploreMassW cleanGamma 1000 (10000 + 40) 40 40 false ctStart.1 ctStart.2.1 ctStart.2.1 ctStart.2.2 =
      (9190118, 9188787, 8107467) := by
  native_decide

/-- The cut classes of the 40-digit clean-tape tree have measure 9,190,118 / 2^40 ≈ 8.4 × 10⁻⁶ of the clean tapes of
width ≥ 2³²: 9,188,787 cut leaves (some above depth 40, where a comparison is decided for every member of the class
but its smallest) and 8,107,467 closed ones. -/
theorem clean_tree_cut_mass40 : (cleanTree 40).cutMass 40 = 9190118 ∧ (cleanTree 40).leaves = (9188787, 8107467) := by
  have h := exploreMassW_eq cleanGamma 1000 (10000 + 40) 40 40 false ctStart.1 ctStart.2.1 ctStart.2.1 ctStart.2.2
  rw [clean_mass_40, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩
