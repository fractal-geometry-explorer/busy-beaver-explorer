import RouteLoop
import LoopFarHalt
open BB6 BB6.Sym

/-! # Far-shape pass starts on routes with two to five passes of the 4-wall loop

`thm/LoopFarHalt.lean` has six families of pass starts with the far shape 15W ≤ 64(W − b), R ≥ 769, every gap at
least 448 and width above 2⁴¹, three of them above 2⁶⁶, that halt and lie in a cut leaf of `passTreeSym` at every depth
(`loopFar`), on the lanes Q + 5 · 2^k − 4 = 2^j with k = 15, 19, 23 and 27.  `Fam.loopOK` (`thm/RouteLoop.lean`) holds
on them with n = 2, 3, 3, 3, 4 and 5, the lane's k = 4n + 7: their round starts in rounds 8i + 5 (i < n) are in
`four_wall_pass`'s class, none in rounds 1 to 8n + 16 has three walls, and the one in round 8n + 17 does
(`loop_far_routes`).  So the far shape that `blank_halt_open_big` puts on the pass start does not bound the number of
passes: pass starts that meet every condition it puts there, the width above 2⁶⁶ included, make three, four and five
passes before the re-entry. -/

namespace BB6

/-- The number of 4-wall passes of each family of `loopFar`. -/
def loopFarN : List Nat := [2, 3, 3, 3, 4, 5]

/-- The round starts to the re-entry on each family, by the kernel (`Fam.ok` is `loopFar_ok`). -/
theorem loopFar_runs : (loopFar.zip loopFarN).all (fun p =>
    symRoundsAll p.1.start.2.2 448 (loopPred p.2) 0 (8 * p.2 + 19) p.1.start.1 p.1.start.2.1) = true := by
  decide +kernel

theorem loopFar_loopOK {F : Fam} {n : Nat} (h : (F, n) ∈ loopFar.zip loopFarN) : F.loopOK n = true := by
  have hm := (List.of_mem_zip h).1
  have hR : loopFar.all (fun F => decide (769 ≤ F.R0)) = true := by decide
  simp only [Fam.loopOK, List.all_eq_true.1 loopFar_ok F hm, List.all_eq_true.1 hR F hm,
    List.all_eq_true.1 loopFar_runs _ h, Bool.and_self]

/-- **Far-shape routes with two to five passes**: for each family of `loopFar` and its n, the pass start with walls
at 449, b₀ and W₀ − R₀ − 1 and width W₀ has R ≥ 769, width above 2⁴¹ and 15W ≤ 64(W − b), every gap at least 448, and
the machine halts from it; its round starts in rounds 8i + 5 (i < n) are in `four_wall_pass`'s class, none in rounds
1 to 8n + 16 has three walls, and the one in round 8n + 17 does. -/
theorem loop_far_routes {F : Fam} {n : Nat} (h : (F, n) ∈ loopFar.zip loopFarN) :
    let ms : List Mark := [⟨.W, 449⟩, ⟨.W, F.b0⟩, ⟨.W, F.W0 - F.R0 - 1⟩]
    769 ≤ F.R0 ∧ 2 ^ 41 < F.W0 ∧ 15 * F.W0 ≤ 64 * (F.W0 - F.b0) ∧ PassStart448 ms F.W0 F.R0 ∧
    (∃ T, steps T (roundStart ms F.W0) = none) ∧
    (∀ i < n, ∃ μ w₁ w₂ w₃ E, roundsZ 1000 (8 * i + 5) ms F.W0 =
        .newRound [⟨.M, μ⟩, ⟨.W, w₁⟩, ⟨.W, w₂⟩, ⟨.W, w₃⟩] E ∧
      448 ≤ μ ∧ μ + 448 ≤ w₁ ∧ w₁ + 448 ≤ w₂ ∧ w₂ + 448 ≤ w₃ ∧ w₃ + 448 ≤ E ∧ μ % 4 = 2 ∧ w₁ % 4 = 2 ∧
      (w₁ + w₂) % 128 = 45 ∧ (w₃ - w₂) % 32 = 1 ∧ (E - w₃) % 32 = 1) ∧
    (∀ r, 0 < r → r < 8 * n + 17 → ∃ ms' W', roundsZ 1000 r ms F.W0 = .newRound ms' W' ∧ NotWWW ms') ∧
    (∃ a' b' c' W', roundsZ 1000 (8 * n + 17) ms F.W0 = .newRound [⟨.W, a'⟩, ⟨.W, b'⟩, ⟨.W, c'⟩] W') := by
  intro ms
  have hm := (List.of_mem_zip h).1
  have hw := of_decide_eq_true (List.all_eq_true.1 loopFar_wide.1 F hm)
  have hb : loopFar.all (fun F => decide (897 ≤ F.b0)) = true := by decide
  have hb' := of_decide_eq_true (List.all_eq_true.1 hb F hm)
  obtain ⟨hR, hP, -, hT, hpass, hnot, h17, -⟩ :=
    Fam.loop_route (loopFar_loopOK h) (a := 449) (t := 0) rfl (by omega) (by omega)
  simp only [Nat.mul_zero, Nat.add_zero] at hP hT hpass hnot h17
  exact ⟨hR, hw.2.1, hw.2.2, hP, hT, hpass, hnot, h17⟩

/-- **Exactly n passes**: on each family of `loopFar`, `Fam.loopOK` fails with one pass more and with one fewer, since
the first three-wall round start after round 0 of the pass start of `loop_far_routes` is in round 8n + 17. -/
theorem loop_far_exact {F : Fam} {n : Nat} (h : (F, n) ∈ loopFar.zip loopFarN) :
    F.loopOK (n + 1) = false ∧ F.loopOK (n - 1) = false := by
  have hm := (List.of_mem_zip h).1
  have hn : 1 ≤ n := by
    have := (List.of_mem_zip h).2
    simp only [loopFarN, List.mem_cons, List.mem_nil_iff, or_false] at this
    omega
  have hb : loopFar.all (fun F => decide (897 ≤ F.b0)) = true := by decide
  have hb' := of_decide_eq_true (List.all_eq_true.1 hb F hm)
  obtain ⟨-, -, -, -, -, -, hnot, h17⟩ := loop_far_routes h
  constructor
  · rw [← Bool.not_eq_true]
    intro hok
    obtain ⟨-, -, -, -, -, hnot', -, -⟩ := Fam.loop_route hok (a := 449) (t := 0) rfl (by omega) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at hnot'
    obtain ⟨a', b', c', W', h⟩ := h17
    obtain ⟨ms', W'', h', hw⟩ := hnot' (8 * n + 17) (by omega) (by omega)
    rw [h] at h'
    cases h'
    exact hw a' b' c' rfl
  · rw [← Bool.not_eq_true]
    intro hok
    obtain ⟨-, -, -, -, -, -, h17', -⟩ := Fam.loop_route hok (a := 449) (t := 0) rfl (by omega) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at h17'
    obtain ⟨a', b', c', W', h⟩ := h17'
    obtain ⟨ms', W'', h', hw⟩ := hnot (8 * (n - 1) + 17) (by omega) (by omega)
    rw [h] at h'
    cases h'
    exact hw a' b' c' rfl

#print axioms loopFar_runs
#print axioms loop_far_routes
#print axioms loop_far_exact

end BB6
