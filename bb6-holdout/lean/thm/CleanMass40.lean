import CleanTheorem
open BB6 BB6.Sym

/-! # The cut classes of the 40-digit clean-tape tree

As `thm/CleanMass.lean`, at 40 digits: the leaf counts and the cut measure of `cleanTree 40`, computed by
`exploreMassW` with `native_decide` (about half an hour of native code).  No theorem about the machine uses them. -/

theorem clean_mass_40 :
    exploreMassW cleanGamma 1000 cleanDrops (10000 + 40) 40 cleanDrops 40 false ctStart.1 ctStart.2.1 ctStart.2.1
      ctStart.2.2 = (9188898, 9188898, 8107588) := by
  native_decide

/-- The cut classes of the 40-digit clean-tape tree have measure 9,188,898 / 2^40 ≈ 8.4 × 10⁻⁶ of the clean tapes of
width ≥ 2³²: 9,188,898 cut leaves, all at depth 40, and 8,107,588 closed ones.  These are exactly the open classes of
the exhaustive check at 40 digits (`../csearch/nrefdfs2.c`). -/
theorem clean_tree_cut_mass40 : (cleanTree 40).cutMass 40 = 9188898 ∧ (cleanTree 40).leaves = (9188898, 8107588) := by
  have h := exploreMassW_eq cleanGamma 1000 cleanDrops (10000 + 40) 40 cleanDrops 40 false ctStart.1 ctStart.2.1
    ctStart.2.1 ctStart.2.2
  rw [clean_mass_40, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩
