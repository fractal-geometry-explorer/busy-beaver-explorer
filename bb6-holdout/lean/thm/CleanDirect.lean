import CleanTheorem
import BB6.CleanRange
open BB6 BB6.Sym

/-! # Clean tapes from 2³² to 2⁴¹, run one by one

`clean_tree_step` makes no claim for the clean tapes in the cut classes of the clean-tape tree.  Below 2⁴¹ they are
few: the 1,660,024 cut classes of `cleanTree 36` (measure 2.4 × 10⁻⁵) have 26,508,327 members of width in
[2³², 2⁴¹).  `clean_direct_ok` runs each of them with the mark model to a wider one-marker clean tape (`rangeOK`,
`BB6/CleanRange.lean`), evaluated with `native_decide`, so it trusts Lean's compiler as well as its kernel.
`clean_step_direct`: every clean tape of width in [2³², 2⁴¹) reaches a wider one, with no exception. -/

theorem clean_direct_ok : rangeOK cleanGamma directWidth (cleanTree 36) = true := by
  native_decide

/-- **Every clean tape of width in [2³², 2⁴¹) reaches a wider one.**  For every even W with 2³² ≤ W < 2⁴¹, the
machine started from the round start G 1, M W − 2 (width W) runs n ≥ 1 rounds of the mark model without halting to
the one-marker clean tape of some width W′ > W. -/
theorem clean_step_direct (W : Nat) (hW : W % 2 = 0) (h1 : cleanGamma ≤ W) (h2 : W < directWidth) :
    ∃ n k W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound [⟨.M, W' - 2⟩] W' ∧
      steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.M, W' - 2⟩] W') ∧ 0 < n ∧ W < W' := by
  have h6 : 6 ≤ W := by simp only [cleanGamma] at h1; omega
  by_cases hc : (cleanTree 36).cutMem [(W : Int) / 2, 0] = true
  · obtain ⟨n, k, W', hr, hk, hn, hlt⟩ := directOK_sound h6 hW (rangeOK_sound clean_direct_ok W hW h1 h2 hc)
    exact ⟨n, k, W', hr, hk, hn, hlt⟩
  · obtain ⟨n, k, ms', W', hr, hk, hc'⟩ := clean_tree_step 36 W hW h1
    rcases hc' with hc' | ⟨hn, rfl, hlt⟩
    · exact absurd hc' hc
    · exact ⟨n, k, W', hr, hk, hn, hlt⟩
