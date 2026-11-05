import LoopFarHalt
import BB6.Count3
open BB6 BB6.Sym

/-! # The 4-wall loop's far members against the machine's conserved count

`blank_pass_mod6` (`BB6/Count3.lean`): a pass start reached from blank tape has W ≡ 2 (mod 6), from the count of 1s
plus state weight, which no step changes mod 3.  The members of `loopFar4` and `loopFar5` (`thm/LoopFarHalt.lean`)
have W ≡ 4 and 0 (mod 6), so the run from blank tape reaches neither (`loopFar45_unreached`): `loop4_far_66` and
`loop5_far_66` meet every condition `blank_halt_open_big` puts on the pass start but this one, which that theorem does
not state.  The members of `loopFar2`, `loopFar3` and `loopFar66` have W ≡ 2 (mod 6) and pass it.

The count does not keep the family off, though.  The far-shape search (`routes/loop4/far_shape.md` in the
halting-classes project files) puts the members of a route at one lane value on a lattice: R = R₁ + P i (P = 2²⁵ on
the four-pass route, 2²⁹ on the five-pass one) and b ≡ b₀ + i · step (mod 2⁹⁸), and Q = W − b + 2R + 22 fixed by the
lane.  Moving `loopFar4`'s member by twice the lattice's short vector
(q, r) = (16,950,295,080, 3,772,763,979,709,939,712) of `far_shape.md`, and `loopFar5`'s by its short vector with
the sign of r turned ((6,747,587,777, −14,701,516,659,416,367,104): q periods of R move b down by r on that route),
gives members with W ≡ 2 (mod 6) on the same lanes and routes (`loopFar45c`), which halt and lie in a cut leaf of
`passTreeSym` at every depth like the others (`Fam.ok`, the model run on each by the kernel).  So with the count too, every condition
the theorems put on the pass start a halt from blank tape needs leaves halting members on the lanes with four and
five passes above 2⁶⁶ (`loop4_far_66c`, `loop5_far_66c`). -/

namespace BB6

/-- **The run from blank tape reaches neither proved member at four and five passes**: their widths are ≡ 4 and
0 (mod 6), whatever the first wall. -/
theorem loopFar45_unreached (k a : Nat) (ha : a % 2 = 1) (h1 : 448 ≤ a) (h2 : a + 448 ≤ 47243874825895927454) :
    steps k ⟨blank, blank, .A⟩ ≠ some (roundStart [⟨.W, a⟩, ⟨.W, 74199323995024383646⟩,
      ⟨.W, 147950097082544601280 - 18101603638022886 - 1⟩] 147950097082544601280) ∧
    steps k ⟨blank, blank, .A⟩ ≠ some (roundStart [⟨.W, a⟩, ⟨.W, 47243874825895927454⟩,
      ⟨.W, 119580288664381470912 - 725281227840787174 - 1⟩] 119580288664381470912) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := blank_pass_mod6 h (by omega) (by omega) (by omega) (by omega) ha (by decide) (by decide) (by decide)
    revert this; decide
  · have := blank_pass_mod6 h (by omega) (by omega) (by omega) (by omega) ha (by decide) (by decide) (by decide)
    revert this; decide

/-- A member of the far shape at Q + 41,943,036 = 2⁶⁶ on the four-pass route (R ≡ 11,899,622 mod 2²⁵), `loopFar4`'s
moved by twice the short vector: R = 1,155,616,650,921,612,006, b/(W − b) = 1.14, width
153,220,594,947,397,302,464 (about 2^67.05), W ≡ 2 (mod 6). -/
def loopFar4c : List Fam := [⟨153220594947397302464, 1155616650921612006, 81744851954444263070, 98, 128⟩]

/-- A member of the far shape at Q + 671,088,636 = 2⁶⁶ on the five-pass route (R ≡ 464,884,454 mod 2²⁹):
R = 4,347,864,831,478,829,798, b/(W − b) = 0.50, width 97,633,604,797,689,018,560 (about 2^66.40), W ≡ 2 (mod 6). -/
def loopFar5c : List Fam := [⟨97633604797689018560, 4347864831478829798, 32542358166479560350, 98, 128⟩]

def loopFar45c : List Fam := loopFar4c ++ loopFar5c

/-- Each on its route and lane, with R ≥ 769, width above 2⁶⁶, 15W ≤ 64(W − b) and W ≡ 2 (mod 6). -/
theorem loopFar45c_shape :
    loopFar4c.map (fun F => (F.R0 % 2 ^ 25, F.W0 - F.b0 + 2 * F.R0 + 22 + 41943036)) = [(11899622, 2 ^ 66)] ∧
    loopFar5c.map (fun F => (F.R0 % 2 ^ 29, F.W0 - F.b0 + 2 * F.R0 + 22 + 671088636)) = [(464884454, 2 ^ 66)] ∧
    loopFar45c.all (fun F => decide (769 ≤ F.R0 ∧ 2 ^ 66 < F.W0 ∧ 15 * F.W0 ≤ 64 * (F.W0 - F.b0) ∧ F.W0 % 6 = 2))
      = true := by
  decide +kernel

/-- Both pass the checks (the close run and the model's run on each, by the kernel). -/
theorem loopFar45c_ok : loopFar45c.all Fam.ok = true := by decide +kernel

/-- **On the four-pass lane, every condition `blank_halt_open_big` puts on the pass start, its width included, and
the count's W ≡ 2 (mod 6)**: a pass start with Q + 41,943,036 = 2⁶⁶, R ≥ 769, width above 2⁶⁶, 15W ≤ 64(W − b),
every gap at least 448, in a cut leaf of `passTreeSym` at every depth, from which the machine halts (`loopFar4c`). -/
theorem loop4_far_66c : ∃ R a b W, 769 ≤ R ∧ 2 ^ 66 < W ∧ 15 * W ≤ 64 * (W - b) ∧ W % 6 = 2 ∧
    W - b + 2 * R + 22 + 41943036 = 2 ^ 66 ∧
    PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R ∧
    (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W : Int) / 2, (R : Int) / 2] = true) ∧
    ∃ T, steps T (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = none := by
  have hF : (⟨153220594947397302464, 1155616650921612006, 81744851954444263070, 98, 128⟩ : Fam) ∈ loopFar45c := by
    simp [loopFar45c, loopFar4c, loopFar5c]
  obtain ⟨hP, hcut, hT⟩ := Fam.open_halt (List.all_eq_true.1 loopFar45c_ok _ hF) (a := 449) (t := 0) rfl (by omega)
    (by decide)
  exact ⟨1155616650921612006, 449, 81744851954444263070, 153220594947397302464, by decide, by decide, by decide,
    by decide, by decide, hP, hcut, hT⟩

/-- **The same on the five-pass lane** Q + 671,088,636 = 2⁶⁶ (`loopFar5c`). -/
theorem loop5_far_66c : ∃ R a b W, 769 ≤ R ∧ 2 ^ 66 < W ∧ 15 * W ≤ 64 * (W - b) ∧ W % 6 = 2 ∧
    W - b + 2 * R + 22 + 671088636 = 2 ^ 66 ∧
    PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R ∧
    (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W : Int) / 2, (R : Int) / 2] = true) ∧
    ∃ T, steps T (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = none := by
  have hF : (⟨97633604797689018560, 4347864831478829798, 32542358166479560350, 98, 128⟩ : Fam) ∈ loopFar45c := by
    simp [loopFar45c, loopFar4c, loopFar5c]
  obtain ⟨hP, hcut, hT⟩ := Fam.open_halt (List.all_eq_true.1 loopFar45c_ok _ hF) (a := 449) (t := 0) rfl (by omega)
    (by decide)
  exact ⟨4347864831478829798, 449, 32542358166479560350, 97633604797689018560, by decide, by decide, by decide,
    by decide, by decide, hP, hcut, hT⟩

#print axioms loopFar45_unreached
#print axioms loopFar45c_shape
#print axioms loopFar45c_ok
#print axioms loop4_far_66c
#print axioms loop5_far_66c

end BB6
