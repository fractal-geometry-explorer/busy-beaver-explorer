import CleanEntryTheorem
import BB6.MassPar
open BB6 BB6.Sym

/-! # The cut classes of the 44-digit clean-tape tree with loop entries, over the widths ≥ 2⁴¹

As `thm/CleanEntryMass.lean`, at 44 digits: the measures and leaf counts of `cleanTreeGE directWidth 44`, the tree
that `blank_halt_clean_entry`, `blank_halt_pass` and `blank_halt_open` use, evaluated with `native_decide`.  The
evaluation is `massPar` (`BB6/MassPar.lean`): `exploreMassWE` followed through its first 8 split levels, and the
subtrees below them computed as parallel tasks; `massPar_eq` proves that this is `exploreMassWE` itself.  No theorem
about the machine uses these numbers. -/

theorem clean_entry_mass_44 :
    massPar directWidth 1000 (cleanEntryOK directWidth) cleanDrops (10000 + 44) 8 36 cleanDrops 44 false
      ctStart.1 ctStart.2.1 ctStart.2.1 ctStart.2.2 = ⟨33928389, 33928389, 32073443, 734274, 23602548493⟩ := by
  native_decide

/-- The cut classes of the 44-digit clean-tape tree with loop entries over the widths ≥ 2⁴¹ have measure
33,928,389 / 2^44 ≈ 1.93 × 10⁻⁶: 33,928,389 cut leaves (all at depth 44), 32,073,443 clean ones, and 734,274 loop
entries that cannot close, of measure 23,602,548,493 / 2^44 ≈ 0.13 %. -/
theorem clean_tree_entry_cut_mass44 : (cleanTreeGE directWidth 44).cutMass 44 = 33928389 ∧
    (cleanTreeGE directWidth 44).leaves = (33928389, 32073443) ∧ (cleanTreeGE directWidth 44).entries = 734274 ∧
    (cleanTreeGE directWidth 44).entryMass 44 = 23602548493 := by
  have h := exploreMassWE_eq directWidth 1000 (cleanEntryOK directWidth) cleanDrops (10000 + 44) 44 cleanDrops 44
    false ctStart.1 ctStart.2.1 ctStart.2.1 ctStart.2.2
  rw [← massPar_eq directWidth 1000 (cleanEntryOK directWidth) cleanDrops (10000 + 44) 8 36, clean_entry_mass_44] at h
  simp only [ETally.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1.symm, Prod.ext h2.symm h3.symm, h4.symm, h5.symm⟩

#print axioms clean_tree_entry_cut_mass44
