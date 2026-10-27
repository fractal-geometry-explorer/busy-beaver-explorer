import CleanEntryTheorem
open BB6 BB6.Sym

/-! # The cut classes of the 36-digit clean-tape tree with loop entries, over the widths ≥ 2²⁴

`blank_halt_clean_entry_kernel` (`thm/CleanEntryHalt.lean`) uses the clean-tape tree with loop entries over the
widths ≥ 2²⁴, `cleanTreeGE (2 ^ 24) d`, above the plain tree over the widths ≥ 2²⁰.  This file evaluates how much it
leaves open at 36 digits, with `exploreMassWE` and `native_decide`: 1,263,032 cut classes, all at depth 36, against
1,660,024 for the plain tree (`thm/CleanKernelMass.lean`).  No theorem about the machine uses them. -/

theorem clean_entry_kernel_mass_36 :
    exploreMassWE (2 ^ 24) 1000 (cleanEntryOK (2 ^ 24)) cleanDrops (10000 + 36) 36 cleanDrops 36 false ctStart.1
      ctStart.2.1 ctStart.2.1 ctStart.2.2 = ⟨1263032, 1263032, 1169027, 28382, 91589786⟩ := by
  native_decide

/-- The cut classes of the 36-digit clean-tape tree with loop entries over the widths ≥ 2²⁴ have measure
1,263,032 / 2^36 ≈ 1.84 × 10⁻⁵: 1,263,032 cut leaves (all at depth 36), 1,169,027 clean ones, and 28,382 loop entries
that cannot close, of measure 91,589,786 / 2^36 ≈ 0.13 %. -/
theorem clean_entry_kernel_cut_mass : (cleanTreeGE (2 ^ 24) 36).cutMass 36 = 1263032 ∧
    (cleanTreeGE (2 ^ 24) 36).leaves = (1263032, 1169027) ∧ (cleanTreeGE (2 ^ 24) 36).entries = 28382 ∧
    (cleanTreeGE (2 ^ 24) 36).entryMass 36 = 91589786 := by
  have h := exploreMassWE_eq (2 ^ 24) 1000 (cleanEntryOK (2 ^ 24)) cleanDrops (10000 + 36) 36 cleanDrops 36 false
    ctStart.1 ctStart.2.1 ctStart.2.1 ctStart.2.2
  rw [clean_entry_kernel_mass_36] at h
  simp only [ETally.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1.symm, Prod.ext h2.symm h3.symm, h4.symm, h5.symm⟩

#print axioms clean_entry_kernel_cut_mass
