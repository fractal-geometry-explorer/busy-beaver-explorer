import CleanTheorem
open BB6 BB6.Sym

/-! # The cut classes of the 40-digit clean-tape tree over the widths ≥ 2⁴¹

As `thm/CleanDirectMass.lean`, at 40 digits: the leaf counts and the cut measure of `cleanTreeG directWidth 40`,
computed by `exploreMassW` with `native_decide`: 9,188,898 cut classes, all at depth 40, and 8,107,588 closed ones,
the same as with the cone W ≥ 2³² (`thm/CleanMass40.lean`) and exactly the open classes of the exhaustive check
(`../csearch/nrefdfs2.c`) at 40 digits.  Two members are dropped (run directly): W = 2⁴¹ + 2, the smallest of the
class W = 2 + 2⁴¹z, where after 39 rounds the round tests 4z = 4, and W = 3 · 2⁴⁰ + 2, the smallest of the class
W = 2⁴⁰ + 2 + 2⁴¹z, where it tests 2 + 4z = 4 (false for every member, but true at z = 1/2, which the cone W ≥ 2⁴¹,
a condition over the rationals, contains).  No theorem about the machine uses them. -/

theorem clean_direct_mass_40 :
    exploreMassW directWidth 1000 cleanDrops (10000 + 40) 40 cleanDrops 40 false ctStart.1 ctStart.2.1 ctStart.2.1
      ctStart.2.2 = (9188898, 9188898, 8107588) := by
  native_decide

/-- The cut classes of the 40-digit clean-tape tree over the widths ≥ 2⁴¹ have measure 9,188,898 / 2^40 ≈
8.4 × 10⁻⁶: 9,188,898 cut leaves, all at depth 40, and 8,107,588 closed ones. -/
theorem clean_direct_cut_mass40 : (cleanTreeG directWidth 40).cutMass 40 = 9188898 ∧
    (cleanTreeG directWidth 40).leaves = (9188898, 8107588) := by
  have h := exploreMassW_eq directWidth 1000 cleanDrops (10000 + 40) 40 cleanDrops 40 false ctStart.1 ctStart.2.1
    ctStart.2.1 ctStart.2.2
  rw [clean_direct_mass_40, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩
