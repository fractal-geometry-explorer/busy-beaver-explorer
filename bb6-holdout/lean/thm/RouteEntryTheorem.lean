import RouteTheorem
import BB6.EntryTree
import BB6.RouteEntry
open BB6 BB6.Sym

/-! # The route tree with loop entries, at every depth

`routeTreeE Γ d` is the route tree of `thm/RouteTheorem.lean` built by the explorer `RTree.exploreE`
(`BB6/EntryTree.lean`), which also stops a path at the first round start that passes `entryOK Γ`
(`BB6/RouteEntry.lean`): a phase-0 pass start with every gap at least 448 and width at least 2²⁴ from which no point
of the class closes through the loop, after full passes or after a half pass and full passes.  Elsewhere it is the
same exploration as `routeTree Γ d`, so its cut classes are among those of `routeTree Γ d`: the classes whose run
enters the loop there and that `routeTree` followed through the loop's passes until its depth ran out are now
settled.  `exploreE_okE` proves that every tree it builds passes the check `RTree.okE`, so `route_tree_entry` holds
for every Γ and every depth with nothing evaluated.  The measure of its cut classes is evaluated in
`thm/RouteEntryMass.lean`. -/

/-- The route tree with loop entries, with cone constant Γ and depth d (a path is also cut after 10,000 rounds). -/
def routeTreeE (Γ d : Nat) : RTree :=
  RTree.exploreE Γ 1000 (entryOK Γ) (10000 + d) d false rtStart.1 rtStart.2.1 rtStart.2.2

theorem route_tree_entry_ok (Γ d : Nat) :
    (routeTreeE Γ d).okE Γ 1000 (entryOK Γ) false rtStart.1 rtStart.2.1 rtStart.2.2 = true :=
  RTree.exploreE_okE _ _ _ _ _ _ _ _ _

/-- **From a two-marker state with wide gaps, the machine reaches the next clean tape or a loop entry that cannot
close, unless the start is in a cut class.**  For every Γ ≥ 8, every depth d, and all naturals m, E with m even, E odd
and both gaps at least Γ (m ≥ Γ, E − m ≥ Γ), the machine started from the round start G 1, M m, M E − 2 (width E) runs
n rounds of the mark model to a round start without halting, and either n ≥ 1 and that round start is a clean tape,
or it is a phase-0 pass start with every gap at least 448 and width at least 2²⁴ from which the loop cannot close
(`EntryNoClose`), or (m/2, (E − 1)/2) lies in one of the cut classes of `routeTreeE Γ d`. -/
theorem route_tree_entry (Γ d m E : Nat) (hΓ : 8 ≤ Γ) (hm : m % 2 = 0) (hE : E % 2 = 1) (h1 : Γ ≤ m)
    (h2 : m + Γ ≤ E) :
    ∃ n k ms' W', roundsZ 1000 n [⟨.M, m⟩, ⟨.M, E - 2⟩] E = .newRound ms' W' ∧
      steps k (roundStart [⟨.M, m⟩, ⟨.M, E - 2⟩] E) = some (roundStart ms' W') ∧
      ((routeTreeE Γ d).cutMem [(m : Int) / 2, ((E : Int) - 1) / 2] = true ∨ (0 < n ∧ cleanTape ms' W') ∨
        EntryNoClose ms' W') := by
  obtain ⟨hy, hs, hW, hwf⟩ := rtStart_point Γ m E hΓ hm hE h1 h2
  obtain ⟨n, k, ms', W', h1', h2', h3'⟩ :=
    RTree.soundE Γ 1000 (entryOK Γ) EntryNoClose (fun _ _ _ _ _ _ h hlen hy hs hW => entryOK_sound h hlen hy hs hW)
      (routeTreeE Γ d) false _ _ _ (route_tree_entry_ok Γ d) _ rfl hy _ _ hs hW hwf
  refine ⟨n, k, ms', W', h1', h2', ?_⟩
  rcases h3' with h | ⟨h, hc⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨by simpa using h, hc⟩)
  · exact Or.inr (Or.inr h)
