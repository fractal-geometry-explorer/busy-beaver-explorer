import RouteTheorem
open BB6 BB6.Sym

/-! # The cut classes of the 40-digit route tree

As `thm/RouteMass.lean`, at 40 digits with Γ = 32,000,000: the leaf counts and the cut measure of
`routeTree 32000000 40`, computed by `exploreMass` with `native_decide` (about half an hour of native code).  They are
the Python certificate's numbers (`../cert/check_tree40*.out`: 2,266,244 clean and 1,682,946 cut leaves, cut measure
1.5306 × 10⁻⁶). -/

theorem route_mass_40 :
    exploreMass 32000000 1000 (10000 + 40) 40 40 false rtStart.1 rtStart.2.1 rtStart.2.2 =
      (1682946, 1682946, 2266244) := by
  native_decide

/-- The cut classes of the 40-digit route tree have measure 1,682,946 / 2^40 ≈ 1.53 × 10⁻⁶ of the start class:
1,682,946 cut leaves (all at depth 40) and 2,266,244 clean ones. -/
theorem route_tree_cut_mass40 : (routeTree 32000000 40).cutMass 40 = 1682946 ∧
    (routeTree 32000000 40).leaves = (1682946, 2266244) := by
  have h := exploreMass_eq 32000000 1000 (10000 + 40) 40 40 false rtStart.1 rtStart.2.1 rtStart.2.2
  rw [route_mass_40, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩
