import RouteEntryHaltC
import CleanBigTheorem
import CleanWideTheorem
import CleanFarTheorem
import BB6.EntryTestsC
open BB6 BB6.Sym

/-! # The clean-tape trees with the variant entry tests, with the narrower closing classes, at every depth

`cleanTreeGS`, `cleanTreeGW`, `cleanTreeGF` and `cleanTreeGB` (`thm/CleanSmallTheorem.lean`,
`thm/CleanWideTheorem.lean`, `thm/CleanFarTheorem.lean`, `thm/CleanBigTheorem.lean`) are the clean-tape tree with loop
entries whose entry test adds the small-end, wide, far and big-end checks to `cleanEntryOK`.  `cleanTreeGSC`,
`cleanTreeGWC`, `cleanTreeGFC` and `cleanTreeGBC` are the same trees with `cleanEntryOKC` in its place
(`BB6/EntryTestsC.lean`): their loop entries cannot close in a class of `closeClassC` (`EntryNoCloseC`).  They are built
by the same proved explorer, `RTree.exploreWE`, so their steps hold at every depth with nothing evaluated.  As with
`cleanTreeGEC` (`thm/RouteEntryHaltC.lean`), the test passes wherever the older one does, so each tree stops every path
that the older one stops at a loop entry, there or earlier, and its cut classes are among the older tree's. -/

/-- `cleanTreeGS` with `cleanSmallOKC`: the clean-tape tree to depth `d` over the clean tapes of width W ≥ Γ whose loop
entries cannot close in a class of `closeClassC` and end at no right end below 178 (`cleanSmallOKC`). -/
def cleanTreeGSC (Γ d : Nat) : RTree :=
  RTree.exploreWE Γ 1000 (cleanSmallOKC Γ) cleanDrops (10000 + d) d cleanDrops false ctStart.1 ctStart.2.1
    ctStart.2.1 ctStart.2.2

theorem clean_tree_smallC_ok (Γ d : Nat) :
    (cleanTreeGSC Γ d).okWE Γ 1000 (cleanSmallOKC Γ) false ctStart.1 ctStart.2.1 ctStart.2.1 ctStart.2.2 = true :=
  RTree.exploreWE_okWE _ _ _ _ _ _ _ _ _ _ _ _

/-- **From a clean tape of width at least Γ, the machine reaches a wider clean tape or a loop entry that cannot close in
a class of `closeClassC` nor end small, unless W/2 is in a cut class.**  `clean_tree_small_step` with `cleanTreeGSC`,
whose entries satisfy `EntryNoCloseC` in place of `EntryNoClose`. -/
theorem clean_tree_small_stepC (Γ d W : Nat) (hΓ : 6 ≤ Γ) (hW : W % 2 = 0) (h : Γ ≤ W) :
    ∃ n k ms' W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound ms' W' ∧
      steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧
      ((cleanTreeGSC Γ d).cutMem [(W : Int) / 2, 0] = true ∨ (0 < n ∧ ms' = [⟨.M, W' - 2⟩] ∧ W < W') ∨
        ((EntryNoCloseC ms' W' ∧ EntryNoSmall ms' W') ∧ W < W')) := by
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
    RTree.soundWE Γ 1000 (cleanSmallOKC Γ)
      (fun ms Wn W0 => (EntryNoCloseC ms Wn ∧ EntryNoSmall ms Wn) ∧ W0 < Wn)
      (fun _ _ _ _ _ _ _ _ h hlen hy hs hW h0 => by
        obtain ⟨h1, h2, h3⟩ := cleanSmallOKC_sound h hlen hy hs hW h0
        exact ⟨⟨h1, h2⟩, h3⟩)
      (cleanTreeGSC Γ d) false _ _ _ _ (clean_tree_smallC_ok Γ d) y rfl hy _ _ _ hs hW' hW' hwf
  refine ⟨n, k, ms', W', h1', h2', ?_⟩
  rcases h3' with h | ⟨h, hc⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨by simpa using h, hc⟩)
  · exact Or.inr (Or.inr h)

/-- `cleanTreeGW` with `cleanWideOKC`: the clean-tape tree to depth `d` over the clean tapes of width W ≥ Γ whose loop
entries cannot close in a class of `closeClassC` and end at no right end below 178, with W ≤ 32R (`cleanWideOKC`). -/
def cleanTreeGWC (Γ d : Nat) : RTree :=
  RTree.exploreWE Γ 1000 (cleanWideOKC Γ) cleanDrops (10000 + d) d cleanDrops false ctStart.1 ctStart.2.1
    ctStart.2.1 ctStart.2.2

theorem clean_tree_wideC_ok (Γ d : Nat) :
    (cleanTreeGWC Γ d).okWE Γ 1000 (cleanWideOKC Γ) false ctStart.1 ctStart.2.1 ctStart.2.1 ctStart.2.2 = true :=
  RTree.exploreWE_okWE _ _ _ _ _ _ _ _ _ _ _ _

/-- **From a clean tape of width at least Γ, the machine reaches a wider clean tape or a wide loop entry that cannot
close in a class of `closeClassC` nor end small, unless W/2 is in a cut class.**  `clean_tree_wide_step` with
`cleanTreeGWC`, whose entries satisfy `EntryNoCloseC` in place of `EntryNoClose`. -/
theorem clean_tree_wide_stepC (Γ d W : Nat) (hΓ : 6 ≤ Γ) (hW : W % 2 = 0) (h : Γ ≤ W) :
    ∃ n k ms' W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound ms' W' ∧
      steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧
      ((cleanTreeGWC Γ d).cutMem [(W : Int) / 2, 0] = true ∨ (0 < n ∧ ms' = [⟨.M, W' - 2⟩] ∧ W < W') ∨
        ((EntryNoCloseC ms' W' ∧ EntryNoSmall ms' W' ∧ EntryWide ms' W') ∧ W < W')) := by
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
    RTree.soundWE Γ 1000 (cleanWideOKC Γ)
      (fun ms Wn W0 => (EntryNoCloseC ms Wn ∧ EntryNoSmall ms Wn ∧ EntryWide ms Wn) ∧ W0 < Wn)
      (fun _ _ _ _ _ _ _ _ h hlen hy hs hW h0 => by
        obtain ⟨h1, h2, h3, h4⟩ := cleanWideOKC_sound h hlen hy hs hW h0
        exact ⟨⟨h1, h2, h3⟩, h4⟩)
      (cleanTreeGWC Γ d) false _ _ _ _ (clean_tree_wideC_ok Γ d) y rfl hy _ _ _ hs hW' hW' hwf
  refine ⟨n, k, ms', W', h1', h2', ?_⟩
  rcases h3' with h | ⟨h, hc⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨by simpa using h, hc⟩)
  · exact Or.inr (Or.inr h)

/-- `cleanTreeGF` with `cleanFarOKC`: the clean-tape tree to depth `d` over the clean tapes of width W ≥ Γ whose loop
entries cannot close in a class of `closeClassC` and end at no right end below 178, with 15W ≤ 64(W − b) and 15W + 26 ≤
32(W − b + R) (`cleanFarOKC`). -/
def cleanTreeGFC (Γ d : Nat) : RTree :=
  RTree.exploreWE Γ 1000 (cleanFarOKC Γ) cleanDrops (10000 + d) d cleanDrops false ctStart.1 ctStart.2.1
    ctStart.2.1 ctStart.2.2

theorem clean_tree_farC_ok (Γ d : Nat) :
    (cleanTreeGFC Γ d).okWE Γ 1000 (cleanFarOKC Γ) false ctStart.1 ctStart.2.1 ctStart.2.1 ctStart.2.2 = true :=
  RTree.exploreWE_okWE _ _ _ _ _ _ _ _ _ _ _ _

/-- **From a clean tape of width at least Γ, the machine reaches a wider clean tape or a far loop entry that cannot
close in a class of `closeClassC` nor end small, unless W/2 is in a cut class.**  `clean_tree_far_step` with
`cleanTreeGFC`, whose entries satisfy `EntryNoCloseC` in place of `EntryNoClose`. -/
theorem clean_tree_far_stepC (Γ d W : Nat) (hΓ : 6 ≤ Γ) (hW : W % 2 = 0) (h : Γ ≤ W) :
    ∃ n k ms' W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound ms' W' ∧
      steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧
      ((cleanTreeGFC Γ d).cutMem [(W : Int) / 2, 0] = true ∨ (0 < n ∧ ms' = [⟨.M, W' - 2⟩] ∧ W < W') ∨
        ((EntryNoCloseC ms' W' ∧ EntryNoSmall ms' W' ∧ EntryFar ms' W') ∧ W < W')) := by
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
    RTree.soundWE Γ 1000 (cleanFarOKC Γ)
      (fun ms Wn W0 => (EntryNoCloseC ms Wn ∧ EntryNoSmall ms Wn ∧ EntryFar ms Wn) ∧ W0 < Wn)
      (fun _ _ _ _ _ _ _ _ h hlen hy hs hW h0 => by
        obtain ⟨h1, h2, h3, h4⟩ := cleanFarOKC_sound h hlen hy hs hW h0
        exact ⟨⟨h1, h2, h3⟩, h4⟩)
      (cleanTreeGFC Γ d) false _ _ _ _ (clean_tree_farC_ok Γ d) y rfl hy _ _ _ hs hW' hW' hwf
  refine ⟨n, k, ms', W', h1', h2', ?_⟩
  rcases h3' with h | ⟨h, hc⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨by simpa using h, hc⟩)
  · exact Or.inr (Or.inr h)

/-- `cleanTreeGB` with `cleanBigOKC 769`: the clean-tape tree to depth `d` over the clean tapes of width W ≥ Γ whose
loop entries cannot close in a class of `closeClassC`, end at no right end below 769 and are far. -/
def cleanTreeGBC (Γ d : Nat) : RTree :=
  RTree.exploreWE Γ 1000 (cleanBigOKC 769 Γ) cleanDrops (10000 + d) d cleanDrops false ctStart.1 ctStart.2.1
    ctStart.2.1 ctStart.2.2

theorem clean_tree_bigC_ok (Γ d : Nat) :
    (cleanTreeGBC Γ d).okWE Γ 1000 (cleanBigOKC 769 Γ) false ctStart.1 ctStart.2.1 ctStart.2.1 ctStart.2.2 = true :=
  RTree.exploreWE_okWE _ _ _ _ _ _ _ _ _ _ _ _

/-- **From a clean tape of width at least Γ, the machine reaches a wider clean tape or a far loop entry that cannot
close in a class of `closeClassC` and ends big, unless W/2 is in a cut class.**  `clean_tree_big_step` with
`cleanTreeGBC`, whose entries satisfy `EntryNoCloseC` in place of `EntryNoClose`. -/
theorem clean_tree_big_stepC (Γ d W : Nat) (hΓ : 6 ≤ Γ) (hW : W % 2 = 0) (h : Γ ≤ W) :
    ∃ n k ms' W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound ms' W' ∧
      steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧
      ((cleanTreeGBC Γ d).cutMem [(W : Int) / 2, 0] = true ∨ (0 < n ∧ ms' = [⟨.M, W' - 2⟩] ∧ W < W') ∨
        ((EntryNoCloseC ms' W' ∧ EntryBigEnd 769 ms' W' ∧ EntryFar ms' W') ∧ W < W')) := by
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
    RTree.soundWE Γ 1000 (cleanBigOKC 769 Γ)
      (fun ms Wn W0 => (EntryNoCloseC ms Wn ∧ EntryBigEnd 769 ms Wn ∧ EntryFar ms Wn) ∧ W0 < Wn)
      (fun _ _ _ _ _ _ _ _ h hlen hy hs hW h0 => by
        obtain ⟨h1, h2, h3, h4⟩ := cleanBigOKC_sound h hlen hy hs hW h0
        exact ⟨⟨h1, h2, h3⟩, h4⟩)
      (cleanTreeGBC Γ d) false _ _ _ _ (clean_tree_bigC_ok Γ d) y rfl hy _ _ _ hs hW' hW' hwf
  refine ⟨n, k, ms', W', h1', h2', ?_⟩
  rcases h3' with h | ⟨h, hc⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨by simpa using h, hc⟩)
  · exact Or.inr (Or.inr h)

#print axioms clean_tree_small_stepC
#print axioms clean_tree_wide_stepC
#print axioms clean_tree_far_stepC
#print axioms clean_tree_big_stepC
