import BB6.RouteExplore
open BB6 BB6.Sym

/-! # The route tree as a theorem, at every depth

`routeTree Γ d` is the two-marker route tree with cone constant Γ and depth d, built by the proved explorer
`RTree.explore` (`BB6/RouteExplore.lean`): from the class of two-marker states G 1, M m, M E − 2 with both gaps at
least Γ, it runs rounds of the symbolic model, splits on the first digit a round does not decide (a shear first when
both coordinates enter it), stops a path at the first clean tape after at least one round, and cuts a path after d
splits. `explore_ok` proves that every tree it builds passes the check `RTree.ok`, so `route_tree_clean` holds for
every Γ and every depth with nothing evaluated (no `native_decide`). The measure of the cut classes is evaluated in
`thm/RouteMass.lean` (36 digits with Γ = 8,000,000 and 40 digits with Γ = 32,000,000, the trees of the Python
certificate). -/

/-- The two-marker start class: m = 2 y₀, E = 1 + 2 y₁; marks M m, M E − 2, width E; cone gaps m and E − m. -/
def rtStart : List SMark × YForm × List YForm :=
  let m : YForm := ⟨0, [2, 0]⟩
  let E : YForm := ⟨1, [0, 2]⟩
  ([⟨.M, m⟩, ⟨.M, E.addc (-2)⟩], E, [m, E.sub m])

/-- The route tree with cone constant Γ and depth d (a path is also cut after 10,000 rounds). -/
def routeTree (Γ d : Nat) : RTree :=
  RTree.explore Γ 1000 (10000 + d) d false rtStart.1 rtStart.2.1 rtStart.2.2

theorem route_tree_ok (Γ d : Nat) : (routeTree Γ d).ok Γ 1000 false rtStart.1 rtStart.2.1 rtStart.2.2 = true :=
  RTree.explore_ok _ _ _ _ _ _ _ _

/-- The two-marker state G 1, M m, M E − 2 (width E; m even, E odd, both gaps at least Γ ≥ 8) is a well-formed round
start that agrees with the start class at the point (m/2, (E − 1)/2) of its cone. -/
theorem rtStart_point (Γ m E : Nat) (hΓ : 8 ≤ Γ) (hm : m % 2 = 0) (hE : E % 2 = 1) (h1 : Γ ≤ m) (h2 : m + Γ ≤ E) :
    inCone rtStart.2.2 Γ [(m : Int) / 2, ((E : Int) - 1) / 2] ∧
      agL [(m : Int) / 2, ((E : Int) - 1) / 2] rtStart.1 [⟨.M, m⟩, ⟨.M, E - 2⟩] ∧
      agN [(m : Int) / 2, ((E : Int) - 1) / 2] rtStart.2.1 E ∧ roundWF [⟨.M, m⟩, ⟨.M, E - 2⟩] E := by
  let y : List Int := [(m : Int) / 2, ((E : Int) - 1) / 2]
  have hy : inCone rtStart.2.2 Γ y := by
    intro t ht
    simp only [rtStart, List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl <;>
      simp only [y, YForm.eval, YForm.sub, YForm.add, YForm.neg, addL, smulL, List.map, dot] <;> omega
  have hs : agL y rtStart.1 [⟨.M, m⟩, ⟨.M, E - 2⟩] := by
    refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, trivial⟩ <;>
      simp only [agN, y, YForm.eval, YForm.addc, dot] <;> omega
  have hW : agN y rtStart.2.1 E := by simp only [agN, y, rtStart, YForm.eval, dot]; omega
  have hwf : roundWF [⟨.M, m⟩, ⟨.M, E - 2⟩] E := by
    simp only [roundWF, rightOK, mval, mlen]
    refine ⟨by omega, ?_, by omega, ?_, by omega, ?_⟩
    all_goals (simp; omega)
  exact ⟨hy, hs, hW, hwf⟩

/-- **From a two-marker state with wide gaps, the machine reaches the next clean tape, unless the start is in a cut
class.**  For every Γ ≥ 8, every depth d, and all naturals m, E with m even, E odd and both gaps at least Γ
(m ≥ Γ, E − m ≥ Γ), the machine started from the round start G 1, M m, M E − 2 (width E) runs n rounds of the mark
model to a round start without halting, and either n ≥ 1 and that round start is a clean tape (the gap at 1, at most
one marker, the end marker), or (m/2, (E − 1)/2) lies in one of the cut classes of `routeTree Γ d`. -/
theorem route_tree_clean (Γ d m E : Nat) (hΓ : 8 ≤ Γ) (hm : m % 2 = 0) (hE : E % 2 = 1) (h1 : Γ ≤ m)
    (h2 : m + Γ ≤ E) :
    ∃ n k ms' W', roundsZ 1000 n [⟨.M, m⟩, ⟨.M, E - 2⟩] E = .newRound ms' W' ∧
      steps k (roundStart [⟨.M, m⟩, ⟨.M, E - 2⟩] E) = some (roundStart ms' W') ∧
      ((routeTree Γ d).cutMem [(m : Int) / 2, ((E : Int) - 1) / 2] = true ∨ (0 < n ∧ cleanTape ms' W')) := by
  obtain ⟨hy, hs, hW, hwf⟩ := rtStart_point Γ m E hΓ hm hE h1 h2
  obtain ⟨n, k, ms', W', h1', h2', h3'⟩ :=
    RTree.sound Γ 1000 (routeTree Γ d) false _ _ _ (route_tree_ok Γ d) _ rfl hy _ _ hs hW hwf
  refine ⟨n, k, ms', W', h1', h2', ?_⟩
  rcases h3' with h | ⟨h, hc⟩
  · exact Or.inl h
  · exact Or.inr ⟨by simpa using h, hc⟩
