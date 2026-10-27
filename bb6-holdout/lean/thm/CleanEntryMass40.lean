import CleanEntryTheorem
import BB6.MassPar
open BB6 BB6.Sym

/-! # The cut classes of the 40-digit clean-tape tree with loop entries, over the widths ≥ 2⁴¹

As `thm/CleanEntryMass.lean`, at 40 digits: the measures and leaf counts of `cleanTreeGE directWidth 40`, the tree
that `blank_halt_clean_entry`, `blank_halt_pass` and `blank_halt_open` use, evaluated with `native_decide`.  The
evaluation is `massPar` (`BB6/MassPar.lean`): `exploreMassWE` followed through its first 8 split levels, and the
subtrees below them computed as parallel tasks; `massPar_eq` proves that this is `exploreMassWE` itself.  No theorem
about the machine uses these numbers. -/

theorem clean_entry_mass_40 :
    massPar directWidth 1000 (cleanEntryOK directWidth) cleanDrops (10000 + 40) 8 32 cleanDrops 40 false
      ctStart.1 ctStart.2.1 ctStart.2.1 ctStart.2.2 = ⟨6582732, 6582732, 6106591, 169631, 1475069898⟩ := by
  native_decide

/-- The cut classes of the 40-digit clean-tape tree with loop entries over the widths ≥ 2⁴¹ have measure
6,582,732 / 2^40 ≈ 5.99 × 10⁻⁶: 6,582,732 cut leaves (all at depth 40), 6,106,591 clean ones, and 169,631 loop
entries that cannot close, of measure 1,475,069,898 / 2^40 ≈ 0.13 %. -/
theorem clean_tree_entry_cut_mass40 : (cleanTreeGE directWidth 40).cutMass 40 = 6582732 ∧
    (cleanTreeGE directWidth 40).leaves = (6582732, 6106591) ∧ (cleanTreeGE directWidth 40).entries = 169631 ∧
    (cleanTreeGE directWidth 40).entryMass 40 = 1475069898 := by
  have h := exploreMassWE_eq directWidth 1000 (cleanEntryOK directWidth) cleanDrops (10000 + 40) 40 cleanDrops 40
    false ctStart.1 ctStart.2.1 ctStart.2.1 ctStart.2.2
  rw [← massPar_eq directWidth 1000 (cleanEntryOK directWidth) cleanDrops (10000 + 40) 8 32, clean_entry_mass_40] at h
  simp only [ETally.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1.symm, Prod.ext h2.symm h3.symm, h4.symm, h5.symm⟩

#print axioms clean_tree_entry_cut_mass40
