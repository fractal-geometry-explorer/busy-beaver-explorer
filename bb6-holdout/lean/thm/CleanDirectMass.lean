import CleanTheorem
open BB6 BB6.Sym

/-! # The cut classes of the 36-digit clean-tape tree over the widths ≥ 2⁴¹

`thm/EndToEndDirect.lean` uses the clean-tape tree with the cone W ≥ 2⁴¹, `cleanTreeG directWidth d`, above the
clean tapes run one by one.  This file evaluates how much it leaves open at 36 digits, with `exploreMassW` and
`native_decide`: 1,660,024 cut classes, all at depth 36 (the cut measure equals the number of cut leaves), the same
as with the cone W ≥ 2³² (`thm/CleanMass.lean`) and exactly the open classes of the exhaustive check at 36 digits
(`../csearch/nrefdfs2.c`).  No theorem about the machine uses them. -/

theorem clean_direct_mass_36 :
    exploreMassW directWidth 1000 cleanDrops (10000 + 36) 36 cleanDrops 36 false ctStart.1 ctStart.2.1 ctStart.2.1
      ctStart.2.2 = (1660024, 1660024, 1507376) := by
  native_decide

/-- The cut classes of the 36-digit clean-tape tree over the widths ≥ 2⁴¹ have measure 1,660,024 / 2^36 ≈ 2.4 × 10⁻⁵:
1,660,024 cut leaves, all at depth 36, and 1,507,376 closed ones. -/
theorem clean_direct_cut_mass : (cleanTreeG directWidth 36).cutMass 36 = 1660024 ∧
    (cleanTreeG directWidth 36).leaves = (1660024, 1507376) := by
  have h := exploreMassW_eq directWidth 1000 cleanDrops (10000 + 36) 36 cleanDrops 36 false ctStart.1 ctStart.2.1
    ctStart.2.1 ctStart.2.2
  rw [clean_direct_mass_36, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩
