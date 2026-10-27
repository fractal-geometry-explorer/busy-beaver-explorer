import RouteEntryTheorem
open BB6 BB6.Sym

/-! # The cut classes of the 36-digit route tree with loop entries

`route_tree_entry` holds at every depth with nothing evaluated; this file evaluates how much it leaves open at 36
digits with Γ = 2²⁶ (every pass start in the cone then has width at least 2²⁷, above the 2²⁴ that an entry needs):
the measures and the leaf counts of `routeTreeE 67108864 36`, computed by `exploreMassE` (the same exploration,
without building the tree) with `native_decide`.  The plain route tree with the same cone constant cuts the classes
of measure 407,087 / 2^36 (as with Γ = 8,000,000, `thm/RouteMass.lean`); with the loop entries 101,855 / 2^36 are left,
all at depth 36. -/

theorem route_entry_mass_36 :
    exploreMassE 67108864 1000 (entryOK 67108864) (10000 + 36) 36 36 false rtStart.1 rtStart.2.1 rtStart.2.2 =
      ⟨101855, 101855, 177001, 5981, 577459574⟩ := by
  native_decide

/-- The cut classes of the 36-digit route tree with loop entries (Γ = 2²⁶) have measure 101,855 / 2^36 ≈ 1.48 × 10⁻⁶
of the start class: 101,855 cut leaves (all at depth 36), 177,001 clean ones, and 5,981 loop entries that cannot
close, of measure 577,459,574 / 2^36 ≈ 0.84 %. -/
theorem route_tree_entry_cut_mass : (routeTreeE 67108864 36).cutMass 36 = 101855 ∧
    (routeTreeE 67108864 36).leaves = (101855, 177001) ∧ (routeTreeE 67108864 36).entries = 5981 ∧
    (routeTreeE 67108864 36).entryMass 36 = 577459574 := by
  have h := exploreMassE_eq 67108864 1000 (entryOK 67108864) (10000 + 36) 36 36 false rtStart.1 rtStart.2.1
    rtStart.2.2
  rw [route_entry_mass_36] at h
  simp only [ETally.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1.symm, Prod.ext h2.symm h3.symm, h4.symm, h5.symm⟩
