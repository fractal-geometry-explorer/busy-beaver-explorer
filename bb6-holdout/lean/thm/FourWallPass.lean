import BB6.SymRound
open BB6 BB6.Sym

/-! # The 4-wall pass: a second loop between the chain's break and the re-entry

From a round start `M μ, W w₁, W w₂, W w₃` of width E (four marks after the gap: a marker and three walls), on the class

  μ ≡ 2 (mod 4), w₁ ≡ 2 (mod 4), w₁ + w₂ ≡ 45 (mod 128), w₃ − w₂ ≡ 1 (mod 32), E − w₃ ≡ 1 (mod 32),

with every gap at least 448, the model's next eight rounds (round starts MWWW, WWWW, BWW, WWWW, BWW, MBW, MWWW, MBW)
end at a round start of the same kind, of width E + 24, with

  ρ′ = (ρ + 15)/16,  σ′ = (σ + 4ρ + 26)/16,  τ′ = (30E + τ + 5σ + 12ρ + 697)/64,  μ′ = (w₁ + w₂ + 19)/32,

where τ = E − w₁, σ = E − w₂ and ρ = E − w₃ are the walls' distances from the end (`four_wall_pass`).  This is an exact
affine map on a residue class, like the loop's full pass on three walls (R → R/16, L₁ → L₁/64): r = ρ − 1 goes to
r/16, s = σ − 2 to (s + 4r)/16, and Λ = 3,969τ − 1,890E − 6,615σ + 19,404ρ − 5,391 to Λ/64, so r³/Λ² is invariant.
Where the image is again in the class the run makes another pass; the halting pass starts of `thm/RouteLoop.lean`
make n of them for every n tried.

The check is one run of `symRoundsZ` on the class (five coordinates, every test decided on the cone) by the kernel;
`symRoundsZ_sound` carries it to every member. -/

namespace BB6.Sym
deriving instance DecidableEq for SMark
deriving instance DecidableEq for SPR
end BB6.Sym

namespace BB6

/-- The class: μ = 2 + 4y₀, w₁ = 2 + 4y₁, w₂ = 43 − 4y₁ + 128y₂, w₃ = w₂ + 1 + 32y₃, E = w₃ + 1 + 32y₄; the cone is
the five gaps μ, w₁ − μ, w₂ − w₁, w₃ − w₂ and E − w₃. -/
def pass4Gaps : List YForm :=
  [⟨2, [4, 0, 0, 0, 0]⟩, ⟨0, [-4, 4, 0, 0, 0]⟩, ⟨41, [0, -8, 128, 0, 0]⟩, ⟨1, [0, 0, 0, 32, 0]⟩, ⟨1, [0, 0, 0, 0, 32]⟩]

def pass4Marks : List SMark :=
  [⟨.M, ⟨2, [4, 0, 0, 0, 0]⟩⟩, ⟨.W, ⟨2, [0, 4, 0, 0, 0]⟩⟩, ⟨.W, ⟨43, [0, -4, 128, 0, 0]⟩⟩,
   ⟨.W, ⟨44, [0, -4, 128, 32, 0]⟩⟩]

def pass4W : YForm := ⟨45, [0, -4, 128, 32, 32]⟩

/-- The round start eight rounds later. -/
def pass4Out : List SMark :=
  [⟨.M, ⟨2, [0, 0, 4, 0, 0]⟩⟩, ⟨.W, ⟨36, [0, -2, 66, 14, 8]⟩⟩, ⟨.W, ⟨67, [0, -4, 128, 30, 22]⟩⟩,
   ⟨.W, ⟨68, [0, -4, 128, 32, 30]⟩⟩]

def pass4OutW : YForm := ⟨69, [0, -4, 128, 32, 32]⟩

/-- The eight rounds on the class (by the kernel). -/
theorem pass4_sym : symRoundsZ pass4Gaps 448 1000 8 pass4Marks pass4W = some (.newRound pass4Out pass4OutW) := by
  decide +kernel

/-- **The 4-wall pass.** -/
theorem four_wall_pass {μ w₁ w₂ w₃ E : Nat} (g0 : 448 ≤ μ) (g1 : μ + 448 ≤ w₁) (g2 : w₁ + 448 ≤ w₂)
    (g3 : w₂ + 448 ≤ w₃) (g4 : w₃ + 448 ≤ E) (c0 : μ % 4 = 2) (c1 : w₁ % 4 = 2) (c2 : (w₁ + w₂) % 128 = 45)
    (c3 : (w₃ - w₂) % 32 = 1) (c4 : (E - w₃) % 32 = 1) :
    ∃ μ' w₁' w₂' w₃', roundsZ 1000 8 [⟨.M, μ⟩, ⟨.W, w₁⟩, ⟨.W, w₂⟩, ⟨.W, w₃⟩] E =
        .newRound [⟨.M, μ'⟩, ⟨.W, w₁'⟩, ⟨.W, w₂'⟩, ⟨.W, w₃'⟩] (E + 24) ∧
      w₃' < E + 24 ∧ 16 * (E + 24 - w₃') = (E - w₃) + 15 ∧
      16 * (E + 24 - w₂') = (E - w₂) + 4 * (E - w₃) + 26 ∧
      64 * (E + 24 - w₁') = 30 * E + (E - w₁) + 5 * (E - w₂) + 12 * (E - w₃) + 697 ∧
      32 * μ' = w₁ + w₂ + 19 := by
  let y : List Int := [((μ : Int) - 2) / 4, ((w₁ : Int) - 2) / 4, ((w₁ : Int) + w₂ - 45) / 128,
    ((w₃ : Int) - w₂ - 1) / 32, ((E : Int) - w₃ - 1) / 32]
  have hy : inCone pass4Gaps 448 y := by
    intro f hf
    simp only [pass4Gaps, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl <;> simp only [y, YForm.eval, dot] <;> omega
  have hs : agL y pass4Marks [⟨.M, μ⟩, ⟨.W, w₁⟩, ⟨.W, w₂⟩, ⟨.W, w₃⟩] := by
    refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, trivial⟩ <;> simp only [agN] <;>
      simp only [y, YForm.eval, dot] <;> omega
  have hW : agN y pass4W E := by simp only [agN, pass4W, y, YForm.eval, dot]; omega
  have hag := symRoundsZ_sound pass4Gaps 448 hy 1000 8 _ _ _ _ _ hs hW pass4_sym
  generalize roundsZ 1000 8 [⟨.M, μ⟩, ⟨.W, w₁⟩, ⟨.W, w₂⟩, ⟨.W, w₃⟩] E = r at hag ⊢
  cases r with
  | newRound ms W' =>
    obtain ⟨hL, hW'⟩ := hag
    match ms, hL with
    | [m0, m1, m2, m3], hL =>
      obtain ⟨⟨t0, p0⟩, ⟨t1, p1⟩, ⟨t2, p2⟩, ⟨t3, p3⟩, -⟩ := hL
      obtain ⟨t0', q0⟩ := m0
      obtain ⟨t1', q1⟩ := m1
      obtain ⟨t2', q2⟩ := m2
      obtain ⟨t3', q3⟩ := m3
      simp only at t0 t1 t2 t3
      subst t0 t1 t2 t3
      simp only [agN, pass4OutW, y, YForm.eval, dot] at p0 p1 p2 p3 hW'
      refine ⟨q0, q1, q2, q3, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have : W' = E + 24 := by omega
        rw [this]
      all_goals omega
  | _ => exact absurd hag id

end BB6

#print axioms BB6.pass4_sym
#print axioms BB6.four_wall_pass
