import LoopTheorem
import BB6.HaltStretch
import BB6.RouteTree

/-!
# A halt from a pass start, for every R, needs a contact after the loop's end

`loop_no_close` states the steps and the end meetings of the run; `loop_no_close_rounds` is the same induction, also
keeping the fact that the mark model covers those rounds (`roundsZ … = .newRound`), which is what `halt_after_rounds`
needs.  With it, `loop_halt_needs_contact` extends `endgame_halt_needs_contact` (`thm/EndgameHalt.lean`) from
R ≤ 4096 to every even R ≥ 2 outside the closing set: if the machine halts from such a phase-0 pass start, it first
completes the whole close-free stretch through the loop's passes, and the mark model, run on from where that stretch
ends, reaches a stuck configuration (a close at the right end or an interior contact).
-/

namespace BB6
open BB6.Sym

/-- `loop_no_close`, keeping that the mark model covers the rounds. -/
theorem loop_no_close_rounds : ∀ (R : Nat), R % 2 = 0 → 2 ≤ R → closingSet.contains R = false →
    ∀ (a b E : Nat), a % 2 = 1 → b % 2 = 0 → E % 2 = 0 → 448 ≤ a → a + 448 ≤ b → b + 448 + R + 1 ≤ E →
    ∃ n ms' W', roundsZ 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E = .newRound ms' W' ∧
      ∀ d ∈ meetsRounds 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E, 3 ≤ d := by
  intro R
  induction R using Nat.strongRecOn with
  | ind R ih =>
    intro hR hR2 hS a b E ha hb hE h1 h2 h3
    by_cases hR4 : R ≤ 4096
    · obtain ⟨n, -, ms', W', -, hr, hm⟩ := endgame_no_close R hR hR2 hR4 hS a b E ha hb hE h1 h2 h3
      exact ⟨n, ms', W', hr, hm⟩
    · obtain ⟨n₁, -, ms₁, W₁, -, hr₁, hm₁, hout⟩ :=
        loop_pass R a b E hR (by omega) ha hb hE h1 h2 h3
      rcases hout with hn | ⟨a', b', R', rfl, ha', hb', hW', hR', g1, g2, g3, g176, hlt, -⟩
      · exact ⟨n₁, ms₁, W₁, hr₁, hm₁⟩
      · obtain ⟨n₂, ms₂, W₂, hr₂, hm₂⟩ :=
          ih R' hlt hR' (by omega) (not_closing g176) a' b' W₁ ha' hb' hW' g1 g2 g3
        refine ⟨n₁ + n₂, ms₂, W₂, ?_, ?_⟩
        · rw [roundsZ_add 1000 n₁ n₂ _ _ _ _ hr₁]; exact hr₂
        · rw [meetsRounds_append 1000 n₁ n₂ _ _ _ _ hr₁]
          intro d hd
          rcases List.mem_append.mp hd with hd | hd
          · exact hm₁ d hd
          · exact hm₂ d hd

/-- **A halt from a pass start needs a contact after the loop's end, for every R.**  If the machine halts from a
phase-0 pass start (walls at a, b, E − R − 1, width E; a odd, b even, E even, R even ≥ 2 outside the closing set,
every gap ≥ 448), the mark model covers a close-free stretch from it (every end meeting at distance ≥ 3) through
every pass the run makes, ending at a round start `ms' W'`; and the model, run on from `ms' W'`, reaches a stuck
configuration: a close at the right end or an interior contact (`stuck_cases`). -/
theorem loop_halt_needs_contact (R : Nat) (hR : R % 2 = 0) (hR2 : 2 ≤ R) (hS : closingSet.contains R = false)
    (a b E : Nat) (ha : a % 2 = 1) (hb : b % 2 = 0) (hE : E % 2 = 0)
    (h1 : 448 ≤ a) (h2 : a + 448 ≤ b) (h3 : b + 448 + R + 1 ≤ E) (T : Nat)
    (hT : steps T (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E) = none) :
    ∃ n ms' W', roundsZ 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E = .newRound ms' W' ∧
      (∀ d ∈ meetsRounds 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E, 3 ≤ d) ∧
      ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t) := by
  obtain ⟨n, ms', W', hr, hm⟩ := loop_no_close_rounds R hR hR2 hS a b E ha hb hE h1 h2 h3
  have hwf : roundWF [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E := by
    simp only [roundWF, rightOK, mval, mlen, iff_true]
    omega
  have hG : noG [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] := by
    intro m hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp
  obtain ⟨-, -, -, -, -, t, ht, htw, hts⟩ := halt_after_rounds 1000 n _ E ms' W' hwf hG hr T hT
  exact ⟨n, ms', W', hr, hm, t, ht, htw, stuck_cases hts⟩

#print axioms loop_halt_needs_contact

end BB6
