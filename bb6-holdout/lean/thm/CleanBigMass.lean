import CleanBigTheorem
open BB6 BB6.Sym

/-! # The cut classes of the 36-digit clean-tape tree whose loop entries end big and far, over the widths ≥ 2⁴¹

`clean_tree_big_step` (`thm/CleanBigTheorem.lean`) holds at every depth with nothing evaluated; this file evaluates
how much the tree that `blank_halt_open_big` uses (`thm/BigEndHalt.lean`), `cleanTreeGB directWidth 36`, leaves open,
with `exploreMassWE` and `native_decide`.  Every loop entry of `cleanTreeGS directWidth 36` (`thm/CleanSmallMass.lean`)
passes `bigEntryOK 769` (no run of full passes from it, nor from its half pass, ends at a right end below 769) and
`farEntryOK`, so the counts are the same: 1,255,963 cut classes, 1,163,068 clean leaves and 28,660 loop entries.  No
theorem about the machine uses them. -/

theorem clean_big_mass_36 :
    exploreMassWE directWidth 1000 (cleanBigOK 769 directWidth) cleanDrops (10000 + 36) 36 cleanDrops 36 false
      ctStart.1 ctStart.2.1 ctStart.2.1 ctStart.2.2 = ⟨1255963, 1255963, 1163068, 28660, 92165830⟩ := by
  native_decide

/-- The cut classes of the 36-digit clean-tape tree whose loop entries end big and far over the widths ≥ 2⁴¹ have
measure 1,255,963 / 2^36 ≈ 1.83 × 10⁻⁵: 1,255,963 cut leaves, 1,163,068 clean ones, and 28,660 loop entries that
cannot close nor end at a right end below 769 and have their middle wall far from the end, of measure
92,165,830 / 2^36 ≈ 0.13 %, as in `cleanTreeGS directWidth 36`. -/
theorem clean_tree_big_cut_mass : (cleanTreeGB directWidth 36).cutMass 36 = 1255963 ∧
    (cleanTreeGB directWidth 36).leaves = (1255963, 1163068) ∧ (cleanTreeGB directWidth 36).entries = 28660 ∧
    (cleanTreeGB directWidth 36).entryMass 36 = 92165830 := by
  have h := exploreMassWE_eq directWidth 1000 (cleanBigOK 769 directWidth) cleanDrops (10000 + 36) 36 cleanDrops 36
    false ctStart.1 ctStart.2.1 ctStart.2.1 ctStart.2.2
  rw [clean_big_mass_36] at h
  simp only [ETally.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1.symm, Prod.ext h2.symm h3.symm, h4.symm, h5.symm⟩

#print axioms clean_tree_big_cut_mass
