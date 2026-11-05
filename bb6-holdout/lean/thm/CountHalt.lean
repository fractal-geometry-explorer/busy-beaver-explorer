import OpenHaltClose
import BB6.Count3
open BB6 BB6.Sym

/-! # The end-to-end statement with the machine's conserved count

`blank_halt_open_big_close` (`thm/OpenHaltClose.lean`) with the widths mod 6 that the count of 1s plus state weight
(`BB6/Count3.lean`) puts on a configuration reached from blank tape: the clean tape a halt needs has W ≡ 4 (mod 6) and
the pass start W₁ ≡ 2 (mod 6).  The trees decide 2-adic classes, each of which holds every residue mod 3, so this is
a condition they cannot state; it is the only conserved count of its kind the searches of the lab notes found
("They pass the machine's conserved count", October 24), and the far members of the 4-wall loop's lanes meet it too
(`loop4_far_66c`, `loop5_far_66c`, `thm/LoopFarCount.lean`). -/

namespace BB6

/-- **The open question with the conserved count**: `blank_halt_open_big_close` with W ≡ 4 (mod 6) at the clean tape
and W₁ ≡ 2 (mod 6) at the pass start. -/
theorem blank_halt_open_big_count (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∃ W k, directWidth ≤ W ∧ W % 6 = 4 ∧ (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      (((∀ d, (cleanTreeGBC directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
          ∃ u, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ u ∧ u.wf ∧ (EndClose u ∨ InteriorContact u)) ∨
        ∃ R a b W₁ t, W < W₁ ∧ 769 ≤ R ∧ 15 * W₁ ≤ 64 * (W₁ - b) ∧ W₁ % 6 = 2 ∧
          PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁ R ∧
          (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W₁ : Int) / 2, (R : Int) / 2] = true) ∧
          steps t (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) ∧
          steps (T - k - t) (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) = none ∧
          ∃ u, Reach ⟨[], 1, [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩], W₁⟩ u ∧ u.wf ∧
            (EndClose u ∨ InteriorContact u)) := by
  obtain ⟨W, k, hBW, hW, hG, hk, hTW, h⟩ := blank_halt_open_big_close T hT
  have hd : directWidth = 2199023255552 := rfl
  have h6 : W % 6 = 4 := blank_clean_mod6 hk (by omega) hW
  refine ⟨W, k, hBW, h6, hG, hk, hTW, ?_⟩
  rcases h with h | ⟨R, a, b, W₁, t, hlt, hR, hsh, hP, hcut, ht, hT₁, hu⟩
  · exact Or.inl h
  · refine Or.inr ⟨R, a, b, W₁, t, hlt, hR, hsh, ?_, hP, hcut, ht, hT₁, hu⟩
    obtain ⟨a', b', hms, pa, pb, pW, pR, hR2, h1, h2, h3⟩ := hP
    simp only [List.cons.injEq, Mark.mk.injEq, and_true, true_and] at hms
    obtain ⟨rfl, rfl⟩ := hms
    exact blank_pass_mod6 (steps_seq hk ht) (by omega) (by omega) (by omega) (by omega) pa pb (by omega) pW

/-- **The open question, with the count.**  `never_halts_of_big_close`'s two questions, asked only of clean tapes with
W ≡ 4 (mod 6) and pass starts with W₁ ≡ 2 (mod 6). -/
theorem never_halts_of_big_count
    (hC : ∀ W, directWidth ≤ W → W % 6 = 4 → (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) →
      (∀ d, (cleanTreeGBC directWidth d).cutMem [(W : Int) / 2, 0] = true) →
      ∀ T, steps T (roundStart [⟨.M, W - 2⟩] W) ≠ none)
    (hP : ∀ W R a b W₁ t, directWidth ≤ W → W % 6 = 4 →
      (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) → W < W₁ → 769 ≤ R →
      15 * W₁ ≤ 64 * (W₁ - b) → W₁ % 6 = 2 → PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁ R →
      (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W₁ : Int) / 2, (R : Int) / 2] = true) →
      steps t (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) →
      ∀ T, steps T (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) ≠ none) :
    ∀ T, steps T ⟨blank, blank, .A⟩ ≠ none := by
  intro T hT
  obtain ⟨W, k, hBW, h6, hG, -, hTW, ⟨hS, -⟩ | ⟨R, a, b, W₁, t, hlt, hR, hsh, h6', hP₁, hcut, ht, hT₁, -⟩⟩ :=
    blank_halt_open_big_count T hT
  · exact hC W hBW h6 hG hS _ hTW
  · exact hP W R a b W₁ t hBW h6 hG hlt hR hsh h6' hP₁ hcut ht _ hT₁

#print axioms blank_halt_open_big_count
#print axioms never_halts_of_big_count

end BB6
