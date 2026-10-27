import CleanTheorem
import PrefixKernel
open BB6 BB6.Sym

/-! # The cut classes of the 36-digit clean-tape tree over the widths ≥ 2²⁰

The end-to-end theorems checked by the kernel alone (`blank_halt_structure_kernel` in `thm/EndToEnd.lean`) start from
the kernel's prefix to the clean tape of width 2²⁰ and use the clean-tape tree with the cone W ≥ 2²⁰,
`cleanTreeG kernelPrefixWidth d`.  This file evaluates how much it leaves open at 36 digits, with `exploreMassW` and
`native_decide`: 1,653,905 cut leaves of measure 2,018,149 / 2³⁶ ≈ 2.9 × 10⁻⁵, against 1,660,086 / 2³⁶ ≈ 2.4 × 10⁻⁵
for the cone W ≥ 2³² (`thm/CleanMass.lean`).  Fewer leaves are cut, but 1,074 of them above full depth, against 7 for
the cone W ≥ 2³²: classes in which a comparison comes out differently for the smallest member, near the cone's bound,
stay cut at every depth.  They start at depth 19 instead of 31, and the two at depth 19 (the class W = 2 + 2²⁰z with
the test 4z = 4, and W = 2¹⁹ + 2 + 2²⁰z with 2 + 4z = 4, true at z = 1/2) carry 262,144 of the measure.  No theorem
about the machine uses this. -/

theorem clean_kernel_mass_36 :
    exploreMassW kernelPrefixWidth 1000 (10000 + 36) 36 36 false ctStart.1 ctStart.2.1 ctStart.2.1 ctStart.2.2 =
      (2018149, 1653905, 1501697) := by
  native_decide

/-- The cut classes of the 36-digit clean-tape tree over the widths ≥ 2²⁰ have measure 2,018,149 / 2^36 ≈ 2.9 × 10⁻⁵:
1,653,905 cut leaves and 1,501,697 closed ones. -/
theorem clean_kernel_cut_mass : (cleanTreeG kernelPrefixWidth 36).cutMass 36 = 2018149 ∧
    (cleanTreeG kernelPrefixWidth 36).leaves = (1653905, 1501697) := by
  have h := exploreMassW_eq kernelPrefixWidth 1000 (10000 + 36) 36 36 false ctStart.1 ctStart.2.1 ctStart.2.1
    ctStart.2.2
  rw [clean_kernel_mass_36, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩
