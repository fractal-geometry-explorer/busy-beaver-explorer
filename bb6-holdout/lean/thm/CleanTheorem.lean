import BB6.RouteExplore
open BB6 BB6.Sym

/-! # The clean-tape tree as a theorem, at every depth

`cleanTree d` is the clean-tape tree to depth `d`, built by the proved explorer `RTree.exploreW`
(`BB6/RouteExplore.lean`): from the class of all clean tapes of width W ≥ 2³², it runs rounds of the symbolic model,
splits on the next binary digit of W/2 when a round is not decided, stops a path at the first one-marker clean tape
decided to be wider than the start, and cuts a path after `d` splits.  Where a round is not decided and no digit
decides it (a comparison at the edge of the cone, true only below the class's smallest member or at it), it runs the
smallest member directly and goes on with the rest of the class (`drop`, at most `cleanDrops` times in a class).
`exploreW_okW` proves that every tree it builds passes the check `RTree.okW`, so `clean_tree_step` holds at every
depth with nothing evaluated (no `native_decide`).  What the depth changes is only how many classes are cut; their
measure at 36 and 40 digits is evaluated in `thm/CleanMass.lean`. -/

/-- The clean-tape start class: W = 2 y₀ (y₁ unused); the marker M W − 2, width W; cone W ≥ Γ. -/
def ctStart : List SMark × YForm × List YForm :=
  let W : YForm := ⟨0, [2, 0]⟩
  ([⟨.M, W.addc (-2)⟩], W, [W])

def cleanGamma : Nat := 4294967296

/-- 2⁴¹: below it the clean tapes in the cut classes are run one by one (`thm/CleanDirect.lean`), and above it the
tree has the cone W ≥ 2⁴¹ (`thm/EndToEndDirect.lean`). -/
def directWidth : Nat := 2199023255552

/-- At most this many members of a class are dropped (run directly) before it is split or cut. -/
def cleanDrops : Nat := 4

/-- The clean-tape tree to depth `d` over the clean tapes of width W ≥ Γ (a path is also cut after 10,000 steps, far
beyond the longest one). -/
def cleanTreeG (Γ d : Nat) : RTree :=
  RTree.exploreW Γ 1000 cleanDrops (10000 + d) d cleanDrops false ctStart.1 ctStart.2.1 ctStart.2.1 ctStart.2.2

/-- The clean-tape tree to depth `d` over the clean tapes of width W ≥ 2³². -/
def cleanTree (d : Nat) : RTree := cleanTreeG cleanGamma d

theorem clean_tree_ok_G (Γ d : Nat) :
    (cleanTreeG Γ d).okW Γ 1000 false ctStart.1 ctStart.2.1 ctStart.2.1 ctStart.2.2 = true :=
  RTree.exploreW_okW _ _ _ _ _ _ _ _ _ _ _

theorem clean_tree_ok (d : Nat) :
    (cleanTree d).okW cleanGamma 1000 false ctStart.1 ctStart.2.1 ctStart.2.1 ctStart.2.2 = true :=
  clean_tree_ok_G cleanGamma d

/-- **From a clean tape of width at least Γ, the machine reaches a wider clean tape, unless W/2 is in a cut class.**
For every Γ ≥ 6, every depth d and every even W ≥ Γ, the machine started from the round start G 1, M W − 2 (width W)
runs n rounds of the mark model to a round start without halting, and either n ≥ 1 and that round start is a
one-marker clean tape of width W′ > W, or W/2 lies in one of the cut classes of `cleanTreeG Γ d` (residue classes of
W/2 modulo powers of two up to 2^d, less the members that a drop on the way ran directly). -/
theorem clean_tree_step_G (Γ d W : Nat) (hΓ : 6 ≤ Γ) (hW : W % 2 = 0) (h : Γ ≤ W) :
    ∃ n k ms' W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound ms' W' ∧
      steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧
      ((cleanTreeG Γ d).cutMem [(W : Int) / 2, 0] = true ∨ (0 < n ∧ ms' = [⟨.M, W' - 2⟩] ∧ W < W')) := by
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
    RTree.soundW Γ 1000 (cleanTreeG Γ d) false _ _ _ _ (clean_tree_ok_G Γ d) y rfl hy _ _ _ hs hW' hW' hwf
  refine ⟨n, k, ms', W', h1', h2', ?_⟩
  rcases h3' with h | ⟨h, hc⟩
  · exact Or.inl h
  · exact Or.inr ⟨by simpa using h, hc⟩

/-- **From a clean tape of width at least 2³², the machine reaches a wider clean tape, unless W/2 is in a cut
class.**  `clean_tree_step_G` with Γ = 2³²: for every depth d and every even W ≥ 2³², the machine started from the
round start G 1, M W − 2 (width W) runs n rounds of the mark model to a round start without halting, and either n ≥ 1
and that round start is a one-marker clean tape of width W′ > W, or W/2 lies in one of the cut classes of
`cleanTree d`. -/
theorem clean_tree_step (d W : Nat) (hW : W % 2 = 0) (h : cleanGamma ≤ W) :
    ∃ n k ms' W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound ms' W' ∧
      steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧
      ((cleanTree d).cutMem [(W : Int) / 2, 0] = true ∨ (0 < n ∧ ms' = [⟨.M, W' - 2⟩] ∧ W < W')) :=
  clean_tree_step_G cleanGamma d W (by decide) hW h
