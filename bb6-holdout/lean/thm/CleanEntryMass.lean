import CleanEntryTheorem
open BB6 BB6.Sym

/-! # The cut classes of the 36-digit clean-tape tree with loop entries, over the widths ≥ 2⁴¹

`clean_tree_entry_step` holds at every depth with nothing evaluated; this file evaluates how much the tree that
`blank_halt_clean_entry` uses (`thm/CleanEntryHalt.lean`), `cleanTreeGE directWidth 36`, leaves open: its measures and
leaf counts, computed by `exploreMassWE` (the same exploration, without building the tree) with `native_decide`.  The
plain clean-tape tree over the same widths cuts 1,660,024 classes (`thm/CleanDirectMass.lean`); with the loop entries
1,255,963 are left, all at depth 36.  No theorem about the machine uses them. -/

theorem clean_entry_mass_36 :
    exploreMassWE directWidth 1000 (cleanEntryOK directWidth) cleanDrops (10000 + 36) 36 cleanDrops 36 false
      ctStart.1 ctStart.2.1 ctStart.2.1 ctStart.2.2 = ⟨1255963, 1255963, 1163068, 28660, 92165830⟩ := by
  native_decide

/-- The cut classes of the 36-digit clean-tape tree with loop entries over the widths ≥ 2⁴¹ have measure
1,255,963 / 2^36 ≈ 1.83 × 10⁻⁵: 1,255,963 cut leaves (all at depth 36), 1,163,068 clean ones, and 28,660 loop entries
that cannot close, of measure 92,165,830 / 2^36 ≈ 0.13 %. -/
theorem clean_tree_entry_cut_mass : (cleanTreeGE directWidth 36).cutMass 36 = 1255963 ∧
    (cleanTreeGE directWidth 36).leaves = (1255963, 1163068) ∧ (cleanTreeGE directWidth 36).entries = 28660 ∧
    (cleanTreeGE directWidth 36).entryMass 36 = 92165830 := by
  have h := exploreMassWE_eq directWidth 1000 (cleanEntryOK directWidth) cleanDrops (10000 + 36) 36 cleanDrops 36
    false ctStart.1 ctStart.2.1 ctStart.2.1 ctStart.2.2
  rw [clean_entry_mass_36] at h
  simp only [ETally.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1.symm, Prod.ext h2.symm h3.symm, h4.symm, h5.symm⟩

#print axioms clean_tree_entry_cut_mass
