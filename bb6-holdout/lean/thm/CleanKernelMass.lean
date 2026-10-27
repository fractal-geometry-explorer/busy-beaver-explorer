import CleanTheorem
import PrefixKernel
open BB6 BB6.Sym

/-! # The cut classes of the 36-digit clean-tape tree over the widths ≥ 2²⁰

The end-to-end theorems checked by the kernel alone (`blank_halt_structure_kernel` in `thm/EndToEnd.lean`) start from
the kernel's prefix to the clean tape of width 2²⁰ and use the clean-tape tree with the cone W ≥ 2²⁰,
`cleanTreeG kernelPrefixWidth d`.  This file evaluates how much it leaves open at 36 digits, with `exploreMassW` and
`native_decide`: 1,660,024 cut leaves, all at depth 36, and 1,507,376 closed ones, the same as with the cones W ≥ 2³²
and W ≥ 2⁴¹ (`thm/CleanMass.lean`, `thm/CleanDirectMass.lean`) and exactly the open classes of the exhaustive check
at 36 digits.  The cone's edge is low here, so the tree drops (runs directly) 1,599 members, from W = 2²⁰ + 2 up;
without the drops, 1,074 leaves were cut above full depth, at classes in which a comparison comes out differently for
the smallest member (the two at depth 19, W = 2 + 2²⁰z with the test 4z = 4 and W = 2¹⁹ + 2 + 2²⁰z with 2 + 4z = 4,
true at z = 1/2, carried 262,144 of a measure of 2,018,149 / 2³⁶).  No theorem about the machine uses this. -/

theorem clean_kernel_mass_36 :
    exploreMassW kernelPrefixWidth 1000 cleanDrops (10000 + 36) 36 cleanDrops 36 false ctStart.1 ctStart.2.1
      ctStart.2.1 ctStart.2.2 = (1660024, 1660024, 1507376) := by
  native_decide

/-- The cut classes of the 36-digit clean-tape tree over the widths ≥ 2²⁰ have measure 1,660,024 / 2^36 ≈ 2.4 × 10⁻⁵:
1,660,024 cut leaves, all at depth 36, and 1,507,376 closed ones. -/
theorem clean_kernel_cut_mass : (cleanTreeG kernelPrefixWidth 36).cutMass 36 = 1660024 ∧
    (cleanTreeG kernelPrefixWidth 36).leaves = (1660024, 1507376) := by
  have h := exploreMassW_eq kernelPrefixWidth 1000 cleanDrops (10000 + 36) 36 cleanDrops 36 false ctStart.1
    ctStart.2.1 ctStart.2.1 ctStart.2.2
  rw [clean_kernel_mass_36, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩
