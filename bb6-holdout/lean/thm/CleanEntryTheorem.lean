import CleanTheorem
import BB6.CleanEntryTree
open BB6 BB6.Sym

/-! # The clean-tape tree with loop entries, at every depth

`cleanTreeGE Γ d` is the clean-tape tree `cleanTreeG Γ d` (`thm/CleanTheorem.lean`) built by `RTree.exploreWE`
(`BB6/CleanEntryTree.lean`): it also stops a path at the first round start that passes `cleanEntryOK`, a phase-0
pass start, decided on the class to be wider than the start, from which no member of the class closes through the
loop (`entryOK`, `BB6/RouteEntry.lean`).  `exploreWE_okWE` proves that every tree it builds passes the check, so
`clean_tree_entry_step` holds at every depth with nothing evaluated. -/

/-- The clean-tape tree with loop entries to depth `d` over the clean tapes of width W ≥ Γ. -/
def cleanTreeGE (Γ d : Nat) : RTree :=
  RTree.exploreWE Γ 1000 (cleanEntryOK Γ) cleanDrops (10000 + d) d cleanDrops false ctStart.1 ctStart.2.1
    ctStart.2.1 ctStart.2.2

theorem clean_tree_entry_ok (Γ d : Nat) :
    (cleanTreeGE Γ d).okWE Γ 1000 (cleanEntryOK Γ) false ctStart.1 ctStart.2.1 ctStart.2.1 ctStart.2.2 = true :=
  RTree.exploreWE_okWE _ _ _ _ _ _ _ _ _ _ _ _

/-- **From a clean tape of width at least Γ, the machine reaches a wider clean tape or a loop entry that cannot
close, unless W/2 is in a cut class.**  For every Γ ≥ 6, every depth d and every even W ≥ Γ, the machine started
from the round start G 1, M W − 2 (width W) runs n rounds of the mark model to a round start without halting, and
either n ≥ 1 and that round start is a one-marker clean tape of width W′ > W, or it is a phase-0 pass start of width
W′ > W from which the loop cannot close (`EntryNoClose`), or W/2 lies in one of the cut classes of `cleanTreeGE Γ d`. -/
theorem clean_tree_entry_step (Γ d W : Nat) (hΓ : 6 ≤ Γ) (hW : W % 2 = 0) (h : Γ ≤ W) :
    ∃ n k ms' W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound ms' W' ∧
      steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧
      ((cleanTreeGE Γ d).cutMem [(W : Int) / 2, 0] = true ∨ (0 < n ∧ ms' = [⟨.M, W' - 2⟩] ∧ W < W') ∨
        (EntryNoClose ms' W' ∧ W < W')) := by
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
    RTree.soundWE Γ 1000 (cleanEntryOK Γ) (fun ms Wn W0 => EntryNoClose ms Wn ∧ W0 < Wn)
      (fun _ _ _ _ _ _ _ _ h hlen hy hs hW h0 => cleanEntryOK_sound h hlen hy hs hW h0)
      (cleanTreeGE Γ d) false _ _ _ _ (clean_tree_entry_ok Γ d) y rfl hy _ _ _ hs hW' hW' hwf
  refine ⟨n, k, ms', W', h1', h2', ?_⟩
  rcases h3' with h | ⟨h, hc⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨by simpa using h, hc⟩)
  · exact Or.inr (Or.inr h)

#print axioms clean_tree_entry_step
