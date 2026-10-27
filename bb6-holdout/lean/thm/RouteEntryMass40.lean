import RouteEntryTheorem
open BB6 BB6.Sym

/-! # The cut classes of the 40-digit route tree with loop entries

As `thm/RouteEntryMass.lean`, at 40 digits (Γ = 2²⁶): the plain route tree with the same cone constant cuts the
classes of measure 1,682,946 / 2^40 (as with Γ = 32,000,000, `thm/RouteMass40.lean`); with the loop entries
357,237 / 2^40 are left, all at depth 40. -/

theorem route_entry_mass_40 :
    exploreMassE 67108864 1000 (entryOK 67108864) (10000 + 40) 40 40 false rtStart.1 rtStart.2.1 rtStart.2.2 =
      ⟨357237, 357237, 599641, 21123, 9239395719⟩ := by
  native_decide

/-- The cut classes of the 40-digit route tree with loop entries (Γ = 2²⁶) have measure 357,237 / 2^40 ≈ 3.25 × 10⁻⁷
of the start class: 357,237 cut leaves (all at depth 40), 599,641 clean ones, and 21,123 loop entries that cannot
close, of measure 9,239,395,719 / 2^40 ≈ 0.84 %. -/
theorem route_tree_entry_cut_mass40 : (routeTreeE 67108864 40).cutMass 40 = 357237 ∧
    (routeTreeE 67108864 40).leaves = (357237, 599641) ∧ (routeTreeE 67108864 40).entries = 21123 ∧
    (routeTreeE 67108864 40).entryMass 40 = 9239395719 := by
  have h := exploreMassE_eq 67108864 1000 (entryOK 67108864) (10000 + 40) 40 40 false rtStart.1 rtStart.2.1
    rtStart.2.2
  rw [route_entry_mass_40] at h
  simp only [ETally.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1.symm, Prod.ext h2.symm h3.symm, h4.symm, h5.symm⟩
