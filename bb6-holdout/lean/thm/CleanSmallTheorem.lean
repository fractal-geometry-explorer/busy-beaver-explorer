import CleanEntryTheorem
import BB6.SmallEnd
open BB6 BB6.Sym

/-! # The clean-tape tree with the small-end check, at every depth

`cleanTreeGS Γ d` is the clean-tape tree with loop entries `cleanTreeGE Γ d` (`thm/CleanEntryTheorem.lean`) whose
entry test also asks that no run of full passes from the entry, nor one after a half pass, ends at a right end below
178, and that the entry is at least 2³⁷ wide (`cleanSmallOK`, `BB6/SmallEnd.lean`).  It is built by the same proved
explorer, `RTree.exploreWE`, so `clean_tree_small_step` holds at every depth with nothing evaluated.  Where the check
fails, the path goes on as in `cleanTreeG Γ d`; at 36 digits over the widths ≥ 2⁴¹ it never fails, and the tree is
`cleanTreeGE directWidth 36` leaf for leaf in its counts (`thm/CleanSmallMass.lean`). -/

/-- The clean-tape tree to depth `d` over the clean tapes of width W ≥ Γ whose loop entries also pass the small-end
check (`cleanSmallOK`). -/
def cleanTreeGS (Γ d : Nat) : RTree :=
  RTree.exploreWE Γ 1000 (cleanSmallOK Γ) cleanDrops (10000 + d) d cleanDrops false ctStart.1 ctStart.2.1
    ctStart.2.1 ctStart.2.2

theorem clean_tree_small_ok (Γ d : Nat) :
    (cleanTreeGS Γ d).okWE Γ 1000 (cleanSmallOK Γ) false ctStart.1 ctStart.2.1 ctStart.2.1 ctStart.2.2 = true :=
  RTree.exploreWE_okWE _ _ _ _ _ _ _ _ _ _ _ _

/-- **From a clean tape of width at least Γ, the machine reaches a wider clean tape or a loop entry that cannot close
nor end small, unless W/2 is in a cut class.**  As `clean_tree_entry_step`, with `cleanTreeGS Γ d` and entries that
also satisfy `EntryNoSmall`. -/
theorem clean_tree_small_step (Γ d W : Nat) (hΓ : 6 ≤ Γ) (hW : W % 2 = 0) (h : Γ ≤ W) :
    ∃ n k ms' W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound ms' W' ∧
      steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧
      ((cleanTreeGS Γ d).cutMem [(W : Int) / 2, 0] = true ∨ (0 < n ∧ ms' = [⟨.M, W' - 2⟩] ∧ W < W') ∨
        ((EntryNoClose ms' W' ∧ EntryNoSmall ms' W') ∧ W < W')) := by
  let y : List Int := [(W : Int) / 2, 0]
  have hy : inCone ctStart.2.2 Γ y := by
    intro t ht
    simp only [ctStart, List.mem_cons, List.mem_nil_iff, or_false] at ht
    subst ht
    simp only [y, YForm.eval, dot]
    omega
  have hs : agL y ctStart.1 [⟨.M, W - 2⟩] := by
    refine ⟨⟨rfl, ?_⟩, trivial⟩
    simp only [agN, y, YForm.eval, YForm.addc, dot]
    omega
  have hW' : agN y ctStart.2.1 W := by simp only [agN, y, ctStart, YForm.eval, dot]; omega
  have hwf : roundWF [⟨.M, W - 2⟩] W := roundWF_one.mpr ⟨by omega, hW⟩
  obtain ⟨n, k, ms', W', h1', h2', h3'⟩ :=
    RTree.soundWE Γ 1000 (cleanSmallOK Γ) (fun ms Wn W0 => (EntryNoClose ms Wn ∧ EntryNoSmall ms Wn) ∧ W0 < Wn)
      (fun _ _ _ _ _ _ _ _ h hlen hy hs hW h0 => by
        obtain ⟨h1, h2, h3⟩ := cleanSmallOK_sound h hlen hy hs hW h0
        exact ⟨⟨h1, h2⟩, h3⟩)
      (cleanTreeGS Γ d) false _ _ _ _ (clean_tree_small_ok Γ d) y rfl hy _ _ _ hs hW' hW' hwf
  refine ⟨n, k, ms', W', h1', h2', ?_⟩
  rcases h3' with h | ⟨h, hc⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨by simpa using h, hc⟩)
  · exact Or.inr (Or.inr h)

#print axioms clean_tree_small_step
