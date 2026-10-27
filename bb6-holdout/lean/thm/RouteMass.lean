import RouteTheorem
open BB6 BB6.Sym

/-! # The cut classes of the 36-digit route tree

`route_tree_clean` holds at every depth with nothing evaluated; this file evaluates how much it leaves open at 36
digits with Γ = 8,000,000: the leaf counts and the cut measure of `routeTree 8000000 36`, computed by `exploreMass`
(the same exploration, without building the tree) with `native_decide`.  They are the Python certificate's numbers
(`../cert/check_tree36.out`: 539,120 clean and 407,087 cut leaves, cut measure 5.9239 × 10⁻⁶). -/

theorem route_mass_36 :
    exploreMass 8000000 1000 (10000 + 36) 36 36 false rtStart.1 rtStart.2.1 rtStart.2.2 = (407087, 407087, 539120) := by
  native_decide

/-- The cut classes of the 36-digit route tree have measure 407,087 / 2^36 ≈ 5.92 × 10⁻⁶ of the start class:
407,087 cut leaves (all at depth 36) and 539,120 clean ones. -/
theorem route_tree_cut_mass : (routeTree 8000000 36).cutMass 36 = 407087 ∧
    (routeTree 8000000 36).leaves = (407087, 539120) := by
  have h := exploreMass_eq 8000000 1000 (10000 + 36) 36 36 false rtStart.1 rtStart.2.1 rtStart.2.2
  rw [route_mass_36, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩
