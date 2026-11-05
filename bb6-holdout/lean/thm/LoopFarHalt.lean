import PassOpenHalt
open BB6 BB6.Sym

/-! # Far-shape pass starts that halt on the 4-wall loop's lanes with two to five passes

The lanes Q + 5 · 2^k − 4 = 2^j or 3 · 2^j (Q = W − b + 2R + 22) carry halting classes for k = 3 and every
k ≡ 2 or 3 (mod 4).  On the lane with k = 4n + 7 the walls make n passes of a loop on four marks between the chain's
break and the re-entry, eight rounds each (the route-completeness side's `four_wall_pass`, with halting families on
Q = 4 + 123 · 2^(4n+7) for n = 0 to 9: `thm/FourWallPass.lean` and `thm/RouteLoop.lean`).  For
n ≥ 1 those families have b close to W, so not the far shape 15W ≤ 64(W − b) that `blank_halt_open_far` puts on the
pass start a halt from blank tape needs.  γ's lane Q + 5,116 (k = 10) has members with that shape wider than 2⁴¹
(`lane769_far_wide`), below the 2⁶⁶ that the untrusted 64-digit check of clean tapes puts on that pass start.  This
file shows that the lanes with two to five passes have such members too, from three passes on above 2⁶⁶.

The search (untrusted; the halting side's far-shape search with the census compiled to native code,
`routes/loop4/far_shape.md` in the halting-classes project files).  The lanes Q + 163,836, Q + 2,621,436,
Q + 41,943,036 and Q + 671,088,636 (k = 15, 19, 23 and 27; two to five passes) carry the routes of the n = 2 to 5
families, at R ≡ 37,606 (mod 2¹⁷), R ≡ 365,286 (mod 2²¹), R ≡ 11,899,622 (mod 2²⁵) and R ≡ 464,884,454 (mod 2²⁹).  At
a lane value 2^j the census at three R of a route, with b fixed mod 2³² to the class at 2⁴¹, finds one class of b
modulo 2^m (m = 57 to 98, about 1.5 bits a scale), and the class moves by the same step from each R to the next one on
the route: the step from the first two R predicts the class at the third, and it is one 2-adic number at every scale.
A lattice search over every R of the route then counts the members with R ≥ 769, every gap at least 448,
15W ≤ 64(W − b) and width above 2⁴¹: on the two-pass route 11, 18, 23, 46, 92, 186, 733 and 3,861 at 2⁴⁰, 2⁴¹, 2⁴²,
2⁴³, 2⁴⁵, 2⁴⁷, 2⁵¹ and 2⁵⁵, and none at 2⁵⁹ or 2⁶³; on the three-pass route 2, 2 and 3 at 2⁴¹, 2⁴² and 2⁴³, and 3,630
at 2⁶⁶; on the four- and five-pass routes none at 2⁴¹ to 2⁴³, and 319 and 19 at 2⁶⁶; at 2⁶⁶ all are wider than 2⁶⁶.
A route's counts stop because the lattice of b's classes over the route has a short vector, q periods of R moving b
by r ((29,361,887, 7,697,741,643,776) on the two-pass route from 2⁵¹ on): the members lie on the lines
qb − ri = const, which thin out as the modulus grows faster than the region, and from 2⁵⁹ on none of them crosses the
far shape's region there; the 3,630 at 2⁶⁶ lie on one line, the 319 on 19.  A census at each member's own R below
finds its class.

`loopFar2`, `loopFar3`, `loopFar66`, `loopFar4` and `loopFar5` hold one member at 2⁴¹ on the two-pass route, two at
2⁴¹ and one at 2⁶⁶ on the three-pass route, and one at 2⁶⁶ on each of the four- and five-pass routes, each as a family
with the first wall free (`Fam`, `thm/PassOpenHalt.lean`).  With `Fam.loopOK` (`thm/RouteLoop.lean`: the round
starts in rounds 8i + 5, i < n, in the 4-wall pass's class, the next three-wall round start in round 8n + 17 and the
re-entry in round 8n + 19), the first has `loopOK 2`, the next three `loopOK 3`, then `loopOK 4` and `loopOK 5`,
and none of them `loopOK` with one pass fewer or more (`thm/RouteLoopFar.lean`: `loop_far_routes`, `loop_far_exact`). -/

namespace BB6

/-- A member of the far shape at Q + 163,836 = 2⁴¹, on the two-pass route at R ≡ 37,606 (mod 2¹⁷):
R = 12,923,998,950, b/(W − b) = 1.27. -/
def loopFar2 : List Fam := [⟨4929578547392, 12923998950, 2756403453598, 60, 78⟩]

/-- Two members of the far shape at Q + 2,621,436 = 2⁴¹, on the three-pass route at R ≡ 365,286 (mod 2²¹):
R = 83,378,934,502 and 324,444,459,750, b/(W − b) = 1.66 and 3.06. -/
def loopFar3 : List Fam :=
  [⟨5413114788032, 83378934502, 3380852022942, 60, 78⟩, ⟨6296036751552, 324444459750, 4745905036958, 60, 78⟩]

/-- A member of the far shape at Q + 2,621,436 = 2⁶⁶, on the same three-pass route: R = 3,795,450,608,325,350,
b/(W − b) = 1.61, width 192,745,493,072,062,232,768 (about 2^67.4), above the 2⁶⁶ of the exhaustive check. -/
def loopFar66 : List Fam := [⟨192745493072062232768, 3795450608325350, 118966107678443298462, 98, 128⟩]

/-- A member of the far shape at Q + 41,943,036 = 2⁶⁶, on the four-pass route at R ≡ 11,899,622 (mod 2²⁵), the n = 4
family's: R = 18,101,603,638,022,886, b/(W − b) = 1.01, width 147,950,097,082,544,601,280 (about 2^67.0). -/
def loopFar4 : List Fam := [⟨147950097082544601280, 18101603638022886, 74199323995024383646, 98, 128⟩]

/-- A member of the far shape at Q + 671,088,636 = 2⁶⁶, on the five-pass route at R ≡ 464,884,454 (mod 2²⁹), the n = 5
family's: R = 725,281,227,840,787,174, b/(W − b) = 0.65, width 119,580,288,664,381,470,912 (about 2^66.7). -/
def loopFar5 : List Fam := [⟨119580288664381470912, 725281227840787174, 47243874825895927454, 98, 128⟩]

/-- The six families. -/
def loopFar : List Fam := loopFar2 ++ loopFar3 ++ loopFar66 ++ loopFar4 ++ loopFar5

/-- Each family's class of R on its route and its lane value, with Q = W − b + 2R + 22. -/
theorem loopFar_shape :
    loopFar2.map (fun F => (F.R0 % 2 ^ 17, F.W0 - F.b0 + 2 * F.R0 + 22 + 163836)) = [(37606, 2 ^ 41)] ∧
    loopFar3.map (fun F => (F.R0 % 2 ^ 21, F.W0 - F.b0 + 2 * F.R0 + 22 + 2621436)) =
      [(365286, 2 ^ 41), (365286, 2 ^ 41)] ∧
    loopFar66.map (fun F => (F.R0 % 2 ^ 21, F.W0 - F.b0 + 2 * F.R0 + 22 + 2621436)) = [(365286, 2 ^ 66)] ∧
    loopFar4.map (fun F => (F.R0 % 2 ^ 25, F.W0 - F.b0 + 2 * F.R0 + 22 + 41943036)) = [(11899622, 2 ^ 66)] ∧
    loopFar5.map (fun F => (F.R0 % 2 ^ 29, F.W0 - F.b0 + 2 * F.R0 + 22 + 671088636)) = [(464884454, 2 ^ 66)] := by
  decide +kernel

/-- Each has R ≥ 769, width above 2⁴¹ (above 2⁶⁶ for `loopFar66`, `loopFar4` and `loopFar5`) and 15W ≤ 64(W − b). -/
theorem loopFar_wide : loopFar.all
      (fun F => decide (769 ≤ F.R0 ∧ 2 ^ 41 < F.W0 ∧ 15 * F.W0 ≤ 64 * (F.W0 - F.b0))) = true ∧
    (loopFar66 ++ loopFar4 ++ loopFar5).all (fun F => decide (2 ^ 66 < F.W0)) = true := by
  decide +kernel

/-- All six pass the checks (the close run and the model's run on each, by the kernel). -/
theorem loopFar_ok : loopFar.all Fam.ok = true := by decide +kernel

/-- **Pass starts with R ≥ 769 that halt, open at every depth, on the lanes with two to five passes of the 4-wall
loop.** -/
theorem loopFar_open_halt {F : Fam} (hF : F ∈ loopFar) {a t : Nat} (ha : a % 2 = 1) (h1 : 448 ≤ a)
    (h2 : a + 448 ≤ F.b0 + 2 ^ F.k * t) :
    769 ≤ F.R0 ∧
    PassStart448 [⟨.W, a⟩, ⟨.W, F.b0 + 2 ^ F.k * t⟩, ⟨.W, F.W0 + 2 ^ F.k * t - F.R0 - 1⟩] (F.W0 + 2 ^ F.k * t)
      F.R0 ∧
    (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, ((F.b0 + 2 ^ F.k * t : Nat) : Int) / 2,
      ((F.W0 + 2 ^ F.k * t : Nat) : Int) / 2, (F.R0 : Int) / 2] = true) ∧
    ∃ T, steps T (roundStart [⟨.W, a⟩, ⟨.W, F.b0 + 2 ^ F.k * t⟩, ⟨.W, F.W0 + 2 ^ F.k * t - F.R0 - 1⟩]
      (F.W0 + 2 ^ F.k * t)) = none := by
  have hR : loopFar.all (fun F => decide (769 ≤ F.R0)) = true := by decide +kernel
  exact ⟨of_decide_eq_true (List.all_eq_true.1 hR F hF), Fam.open_halt (List.all_eq_true.1 loopFar_ok F hF) ha h1 h2⟩

/-- **On the two-pass lane, every condition `blank_halt_open_big` puts on the pass start, its width included**: a pass
start with Q + 163,836 = 2⁴¹, R ≥ 769, width above 2⁴¹ and 15W ≤ 64(W − b), every gap at least 448, in a cut leaf of
`passTreeSym` at every depth, from which the machine halts (walls 449, 2,756,403,453,598 and 4,916,654,548,441, width
4,929,578,547,392, about 2^42.2, R = 12,923,998,950: `loopFar2`). -/
theorem loop2_far_wide : ∃ R a b W, 769 ≤ R ∧ 2 ^ 41 < W ∧ 15 * W ≤ 64 * (W - b) ∧
    W - b + 2 * R + 22 + 163836 = 2 ^ 41 ∧
    PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R ∧
    (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W : Int) / 2, (R : Int) / 2] = true) ∧
    ∃ T, steps T (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = none := by
  have hF : (⟨4929578547392, 12923998950, 2756403453598, 60, 78⟩ : Fam) ∈ loopFar := by
    simp [loopFar, loopFar2, loopFar3, loopFar66, loopFar4, loopFar5]
  obtain ⟨hR, hP, hcut, hT⟩ := loopFar_open_halt hF (a := 449) (t := 0) rfl (by omega) (by decide)
  exact ⟨12923998950, 449, 2756403453598, 4929578547392, hR, by decide, by decide, by decide, hP, hcut, hT⟩

/-- **The same on the three-pass lane** Q + 2,621,436 = 2⁴¹ (walls 449, 3,380,852,022,942 and 5,329,735,853,529,
width 5,413,114,788,032, about 2^42.3, R = 83,378,934,502: `loopFar3`'s first family). -/
theorem loop3_far_wide : ∃ R a b W, 769 ≤ R ∧ 2 ^ 41 < W ∧ 15 * W ≤ 64 * (W - b) ∧
    W - b + 2 * R + 22 + 2621436 = 2 ^ 41 ∧
    PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R ∧
    (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W : Int) / 2, (R : Int) / 2] = true) ∧
    ∃ T, steps T (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = none := by
  have hF : (⟨5413114788032, 83378934502, 3380852022942, 60, 78⟩ : Fam) ∈ loopFar := by
    simp [loopFar, loopFar2, loopFar3, loopFar66, loopFar4, loopFar5]
  obtain ⟨hR, hP, hcut, hT⟩ := loopFar_open_halt hF (a := 449) (t := 0) rfl (by omega) (by decide)
  exact ⟨83378934502, 449, 3380852022942, 5413114788032, hR, by decide, by decide, by decide, hP, hcut, hT⟩

/-- **The same above the exhaustive check's 2⁶⁶**: a pass start on the three-pass lane, Q + 2,621,436 = 2⁶⁶, with
R ≥ 769, width above 2⁶⁶ and 15W ≤ 64(W − b), every gap at least 448, in a cut leaf of `passTreeSym` at every depth,
from which the machine halts (walls 449, 118,966,107,678,443,298,462 and 192,741,697,621,453,907,417, width
192,745,493,072,062,232,768, R = 3,795,450,608,325,350: `loopFar66`).  With the untrusted 64-digit check in place of
`stepsBelow_direct` the pass start a halt from blank tape needs is wider than 2⁶⁶; this one is. -/
theorem loop3_far_66 : ∃ R a b W, 769 ≤ R ∧ 2 ^ 66 < W ∧ 15 * W ≤ 64 * (W - b) ∧
    W - b + 2 * R + 22 + 2621436 = 2 ^ 66 ∧
    PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R ∧
    (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W : Int) / 2, (R : Int) / 2] = true) ∧
    ∃ T, steps T (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = none := by
  have hF : (⟨192745493072062232768, 3795450608325350, 118966107678443298462, 98, 128⟩ : Fam) ∈ loopFar := by
    simp [loopFar, loopFar2, loopFar3, loopFar66, loopFar4, loopFar5]
  obtain ⟨hR, hP, hcut, hT⟩ := loopFar_open_halt hF (a := 449) (t := 0) rfl (by omega) (by decide)
  exact ⟨3795450608325350, 449, 118966107678443298462, 192745493072062232768, hR, by decide, by decide, by decide, hP,
    hcut, hT⟩

/-- **The same on the four-pass lane** Q + 41,943,036 = 2⁶⁶ (walls 449, 74,199,323,995,024,383,646 and
147,931,995,478,906,578,393, width 147,950,097,082,544,601,280, R = 18,101,603,638,022,886: `loopFar4`). -/
theorem loop4_far_66 : ∃ R a b W, 769 ≤ R ∧ 2 ^ 66 < W ∧ 15 * W ≤ 64 * (W - b) ∧
    W - b + 2 * R + 22 + 41943036 = 2 ^ 66 ∧
    PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R ∧
    (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W : Int) / 2, (R : Int) / 2] = true) ∧
    ∃ T, steps T (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = none := by
  have hF : (⟨147950097082544601280, 18101603638022886, 74199323995024383646, 98, 128⟩ : Fam) ∈ loopFar := by
    simp [loopFar, loopFar2, loopFar3, loopFar66, loopFar4, loopFar5]
  obtain ⟨hR, hP, hcut, hT⟩ := loopFar_open_halt hF (a := 449) (t := 0) rfl (by omega) (by decide)
  exact ⟨18101603638022886, 449, 74199323995024383646, 147950097082544601280, hR, by decide, by decide, by decide, hP,
    hcut, hT⟩

/-- **The same on the five-pass lane** Q + 671,088,636 = 2⁶⁶ (walls 449, 47,243,874,825,895,927,454 and
118,855,007,436,540,683,737, width 119,580,288,664,381,470,912, R = 725,281,227,840,787,174: `loopFar5`). -/
theorem loop5_far_66 : ∃ R a b W, 769 ≤ R ∧ 2 ^ 66 < W ∧ 15 * W ≤ 64 * (W - b) ∧
    W - b + 2 * R + 22 + 671088636 = 2 ^ 66 ∧
    PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R ∧
    (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W : Int) / 2, (R : Int) / 2] = true) ∧
    ∃ T, steps T (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = none := by
  have hF : (⟨119580288664381470912, 725281227840787174, 47243874825895927454, 98, 128⟩ : Fam) ∈ loopFar := by
    simp [loopFar, loopFar2, loopFar3, loopFar66, loopFar4, loopFar5]
  obtain ⟨hR, hP, hcut, hT⟩ := loopFar_open_halt hF (a := 449) (t := 0) rfl (by omega) (by decide)
  exact ⟨725281227840787174, 449, 47243874825895927454, 119580288664381470912, hR, by decide, by decide, by decide,
    hP, hcut, hT⟩

#print axioms loopFar_shape
#print axioms loopFar_wide
#print axioms loopFar_open_halt
#print axioms loop2_far_wide
#print axioms loop3_far_wide
#print axioms loop3_far_66
#print axioms loop4_far_66
#print axioms loop5_far_66

end BB6
