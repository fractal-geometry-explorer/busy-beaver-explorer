import CleanWideTheorem
open BB6 BB6.Sym

/-! # The cut classes of the 36-digit clean-tape tree with wide loop entries, over the widths ≥ 2⁴¹

`clean_tree_wide_step` (`thm/CleanWideTheorem.lean`) holds at every depth with nothing evaluated; this file evaluates
how much the tree that `blank_halt_open_wide` uses (`thm/WideHalt.lean`), `cleanTreeGW directWidth 36`, leaves open,
with `exploreMassWE` and `native_decide`.  Every loop entry of `cleanTreeGS directWidth 36` (`thm/CleanSmallMass.lean`)
has W ≤ 32R, so the counts are the same: 1,255,963 cut classes, 1,163,068 clean leaves and 28,660 loop entries.  No
theorem about the machine uses them. -/

theorem clean_wide_mass_36 :
    exploreMassWE directWidth 1000 (cleanWideOK directWidth) cleanDrops (10000 + 36) 36 cleanDrops 36 false
      ctStart.1 ctStart.2.1 ctStart.2.1 ctStart.2.2 = ⟨1255963, 1255963, 1163068, 28660, 92165830⟩ := by
  native_decide

/-- The cut classes of the 36-digit clean-tape tree with wide loop entries over the widths ≥ 2⁴¹ have measure
1,255,963 / 2^36 ≈ 1.83 × 10⁻⁵: 1,255,963 cut leaves, 1,163,068 clean ones, and 28,660 loop entries that cannot close
nor end at a right end below 178 and have W ≤ 32R, of measure 92,165,830 / 2^36 ≈ 0.13 %, as in
`cleanTreeGS directWidth 36`. -/
theorem clean_tree_wide_cut_mass : (cleanTreeGW directWidth 36).cutMass 36 = 1255963 ∧
    (cleanTreeGW directWidth 36).leaves = (1255963, 1163068) ∧ (cleanTreeGW directWidth 36).entries = 28660 ∧
    (cleanTreeGW directWidth 36).entryMass 36 = 92165830 := by
  have h := exploreMassWE_eq directWidth 1000 (cleanWideOK directWidth) cleanDrops (10000 + 36) 36 cleanDrops 36
    false ctStart.1 ctStart.2.1 ctStart.2.1 ctStart.2.2
  rw [clean_wide_mass_36] at h
  simp only [ETally.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1.symm, Prod.ext h2.symm h3.symm, h4.symm, h5.symm⟩

#print axioms clean_tree_wide_cut_mass
