import PassHalt
import LoopClose

/-!
# A halt from a pass start, with end meetings at distance 2 passed

`pass_halt_chain` (`thm/PassHalt.lean`) stops at a pass start whose left countdown is in R's class of `closeClass`,
and the pass-start trees for R < 178 end a path at a `close` leaf where a round is decided as something other than a
new round start and the start's left countdown is decidedly in that class.  An end meeting at distance 2 is not a close
(`thm/LoopClose.lean`): a close needs R in {2, 4, 8, 16, 32, 48} and L₁ in R's class of `closeClassC`.  The trees
`passTreeRC` are built by the same explorer with `closeClassC R` as the class of their `close` leaves.  The class enters
the explorer only there (`passAct`: a round decided as something other than a new round start ends the path at
`close` when the left countdown is decidedly in the class, else at `cut`), so each has the shape of `passTreeR`, with a
`cut` leaf where `passTreeR` has a `close` leaf whose countdown is not decidedly in the narrower class.  Outside R = 8,
16, 24, 32, 64 and 176 the two classes, the two trees and the two cuts are the same (`passCutC_iff_of`), and from
R = 178 on both are the cut of `passTreeSym` (`passCutC_iff`).

`pass_next_close` and `pass_halt_chain_close` are `pass_next` and `pass_halt_chain` with these trees: a halt from a pass
start of width at least 2¹³ follows the loop's chain to a last pass start in R's class of `closeClassC`
(`InCloseClassC`), or cut at every depth of its tree (`PassCutC`), or goes on to a wider clean tape.
-/

namespace BB6
open BB6.Sym

/-- The pass-start tree for the pass starts with right end R < 178 (the class `startR R`), `d` splits deep, with the
classes of `closeClassC` at its `close` leaves. -/
def passTreeRC (R d : Nat) : PTree :=
  PTree.explore 448 1000 3 (closeClassC R) (10000 + d) d passCleaves false true 0 (startR R).1 (startR R).2.1
    (startR R).2.2 (startE R).2

theorem passTreeRC_ok (R d : Nat) :
    (passTreeRC R d).ok 448 1000 3 (closeClassC R) false true 0 (startR R).1 (startR R).2.1 (startR R).2.2
      (startE R).2 = true :=
  PTree.explore_ok 448 1000 3 (closeClassC R) (10000 + d) d passCleaves false true 0 (startR R).1 (startR R).2.1
    (startR R).2.2 (startE R).2

/-- `PassCut` with the trees `passTreeRC`: the pass start with walls at a, b and W − R − 1, width W and right end R
lies in a cut leaf of its pass-start tree `d` splits deep (at the point ((a − 1)/2, b/2, W/2), and R/2 for R ≥ 178). -/
def PassCutC (d R a b W : Nat) : Prop :=
  if R < 178 then (passTreeRC R d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W : Int) / 2] = true
  else (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W : Int) / 2, (R : Int) / 2] = true

/-- Outside R = 8, 16, 24, 32, 64 and 176, where `closeClassC` is `closeClass`, `PassCutC` is `PassCut`. -/
theorem passCutC_iff_of {d R a b W : Nat} (h : closeTreeRs.contains R = false) :
    PassCutC d R a b W ↔ PassCut d R a b W := by
  simp only [PassCutC, PassCut, passTreeRC, passTreeR, closeClassC_eq h]

/-- From R = 178 on, `PassCutC` is `PassCut`: both are the cut of `passTreeSym`. -/
theorem passCutC_iff {d R a b W : Nat} (hR : 178 ≤ R) : PassCutC d R a b W ↔ PassCut d R a b W := by
  simp only [PassCutC, PassCut, show ¬ R < 178 by omega, ↓reduceIte]

/-- **From a pass start to the next checkpoint, with end meetings at distance 2 passed.**  For every depth d and every
phase-0 pass start with right end R and every gap at least 448: either R is in {2, 4, 8, 16, 32, 48} and the left
countdown is in R's class of `closeClassC` (`InCloseClassC`); or the start lies in a cut leaf of its pass-start tree
d splits deep (`PassCutC`); or the machine runs r rounds without halting, to a landing of the loop's chain (`Landing`,
with the step's exact map) with every end meeting on the way at distance at least 3, or, after at least one round, to a
one-marker clean tape wider than the start. -/
theorem pass_next_close (d R a b W : Nat) (hP : PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R) :
    InCloseClassC [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R ∨ PassCutC d R a b W ∨
    ∃ r kk ms' W', steps kk (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = some (roundStart ms' W') ∧
      roundsZ 1000 r [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W = .newRound ms' W' ∧
      (((∀ e ∈ meetsRounds 1000 r [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W, 3 ≤ e) ∧
          Landing r W R (passL1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) ms' W') ∨
        (0 < r ∧ CleanTape ms' W' ∧ W < W')) := by
  by_cases hR178 : 178 ≤ R
  · -- the tree for every R ≥ 178, as in `pass_next`
    rcases pass_next d R a b W hP with ⟨-, -, m, c, -, hc, -⟩ | hcut | h
    · have h1 : R = 2 ∨ R = 4 ∨ R = 8 ∨ R = 16 ∨ R = 24 ∨ R = 32 ∨ R = 48 ∨ R = 64 ∨ R = 176 := by
        simpa [closingSet] using closeClass_closing hc
      omega
    · exact Or.inr (Or.inl ((passCutC_iff hR178).mpr hcut))
    · exact Or.inr (Or.inr h)
  · -- the tree for R, with the classes of `closeClassC`
    obtain ⟨a₀, b₀, hms, ha, hb, hE, hR, hR2, h1, h2, h3⟩ := hP
    simp only [List.cons.injEq, Mark.mk.injEq, true_and, and_true] at hms
    obtain ⟨rfl, rfl⟩ := hms
    let y : List Int := [((a : Int) - 1) / 2, (b : Int) / 2, (W : Int) / 2]
    have hy : inCone (startR R).2.2 448 y := by
      intro f hf
      simp only [startR, List.mem_cons, List.mem_nil_iff, or_false] at hf
      rcases hf with rfl | rfl | rfl <;>
        simp only [y, YForm.eval, YForm.sub, YForm.add, YForm.neg, YForm.addc, addL, smulL, List.map, dot] <;> omega
    have hs : agL y (startR R).1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] := by
      refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, trivial⟩ <;>
        simp only [agN, y, YForm.eval, YForm.addc, dot] <;> omega
    have hW : agN y (startR R).2.1 W := by simp only [agN, y, startR, YForm.eval, dot]; omega
    have hf : (startE R).2.Ag y W R (loopL1 b (W - R - 1) W) := by
      refine ⟨?_, ?_, ?_⟩
      · simp only [agN, y, startE, YForm.eval, dot]; omega
      · simp [agN, startE, YForm.const, YForm.eval]
      · simp only [startE, eval_L1Form, loopL1]
        simp only [y, YForm.eval, YForm.addc, dot]
        omega
    rcases PTree.sound 448 1000 3 (closeClassC R) (passTreeRC R d) false true 0 (startR R).1 (startR R).2.1
        (startR R).2.2 (startE R).2 (passTreeRC_ok R d) y rfl hy _ W W R _ hs hW hf (fun h => by cases h) with
      hc | ⟨m, c, hm, hl⟩ | ⟨r, kk, ms', W', hk, hr, hev⟩
    · right; left
      simp only [PassCutC, show R < 178 by omega, ↓reduceIte]
      exact hc
    · left
      exact ⟨a, b, m, c, rfl, hm, hl⟩
    · right; right
      refine ⟨r, kk, ms', W', hk, hr, ?_⟩
      rcases hev with ⟨-, hm, hl⟩ | ⟨h0, hc, hlt⟩
      · simp only [Nat.zero_add] at hl
        exact Or.inl ⟨hm, hl⟩
      · exact Or.inr ⟨by omega, hc, hlt⟩

/-- **A halt from a wide pass start: the checkpoints, with end meetings at distance 2 passed.**  `pass_halt_chain`
with `pass_next_close`: if the machine halts T steps after a phase-0 pass start of width W ≥ 2¹³ with right end R and
every gap at least 448 (and, if W ≡ 2 mod 4, the middle wall b at least 896 from the end), then its run from there
follows the loop's chain (`LoopChain`) to a last pass start with walls a₁, b₁, W₁ − R₁ − 1, again with every gap at
least 448 (and the middle wall at least 896 from the end if W₁ ≡ 2 mod 4), where: R₁ is in {2, 4, 8, 16, 32, 48} and
the left countdown is in R₁'s class of `closeClassC` (`InCloseClassC`), and the mark model, run on from there, reaches
a stuck configuration; or the last pass start lies in a cut leaf of its pass-start tree at every depth (`PassCutC`); or
the run, from the last pass start, reaches a one-marker clean tape of even width W′ > W after k steps, 0 < k < T, and
halts T − k steps after it. -/
theorem pass_halt_chain_close (T : Nat) : ∀ (R a b W : Nat),
    PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R →
    2 ^ 13 ≤ W → (W % 4 = 2 → b + 896 ≤ W) →
    steps T (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = none →
    ∃ ks a₁ b₁ W₁ R₁,
      LoopChain [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R ks [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁ R₁ ∧
      (W₁ % 4 = 2 → b₁ + 896 ≤ W₁) ∧
      ((InCloseClassC [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁ R₁ ∧
          ∃ t, Reach ⟨[], 1, [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩], W₁⟩ t ∧ t.wf ∧
            (EndClose t ∨ InteriorContact t)) ∨
        (∀ d, PassCutC d R₁ a₁ b₁ W₁) ∨
        ∃ k W', 0 < k ∧ k < T ∧ W < W' ∧ W' % 2 = 0 ∧
          steps k (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = some (roundStart [⟨.M, W' - 2⟩] W') ∧
          steps (T - k) (roundStart [⟨.M, W' - 2⟩] W') = none) := by
  induction T using Nat.strongRecOn with
  | ind T ih =>
    intro R a b W hP hW hh hT
    obtain ⟨hwf, hG⟩ := hP.wf
    by_cases hc : InCloseClassC [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R
    · obtain ⟨t, ht, htw, hts⟩ := round_halt_needs_contact _ W T hwf hG hT
      exact ⟨[], a, b, W, R, .nil hP, hh, Or.inl ⟨hc, t, ht, htw, stuck_cases hts⟩⟩
    by_cases hcut : ∀ d, PassCutC d R a b W
    · exact ⟨[], a, b, W, R, .nil hP, hh, Or.inr (Or.inl hcut)⟩
    obtain ⟨d, hd⟩ := Classical.not_forall.mp hcut
    rcases pass_next_close d R a b W hP with hc' | hd' | ⟨r, kk, ms', W', hk, hr, hev⟩
    · exact absurd hc' hc
    · exact absurd hd' hd
    obtain ⟨k, hkT, hk', hT', -, -⟩ := halt_after_rounds 1000 r _ W ms' W' hwf hG hr T hT
    rcases hev with ⟨hm, hl⟩ | ⟨-, hct, hlt⟩
    · -- a landing, again a pass start with every gap at least 448: follow the chain on from it
      obtain ⟨R', hP'⟩ := landing_wide hP hW hh hl
      obtain ⟨hW4, kind, hmap⟩ := landing_passStart hl hP'
      have hlt : W < W' := by cases kind <;> simp only [StepMap] at hmap <;> omega
      have hk1 : 0 < k := by
        rcases Nat.eq_zero_or_pos k with rfl | h0
        · simp only [steps, Option.some.injEq] at hk'
          exact absurd hk' (passStart_ne hP hP' hlt)
        · exact h0
      obtain ⟨a', b', rfl, -⟩ := id hP'
      obtain ⟨ks, a₁, b₁, W₁, R₁, hch, hh₁, hend⟩ :=
        ih (T - k) (by omega) R' a' b' W' hP' (Nat.le_trans hW (Nat.le_of_lt hlt)) (fun h => by omega) hT'
      refine ⟨kind :: ks, a₁, b₁, W₁, R₁, .cons kind r kk hP hk hr hm hW4 hmap hch, hh₁, ?_⟩
      rcases hend with h | h | ⟨k₂, W₂, hk₂, hkT₂, hlt₂, hpar₂, hs₂, hT₂⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · refine Or.inr (Or.inr ⟨k + k₂, W₂, by omega, by omega, by omega, hpar₂, steps_seq hk' hs₂, ?_⟩)
        rw [show T - (k + k₂) = T - k - k₂ by omega]
        exact hT₂
    · -- a one-marker clean tape, wider than the start
      have hms' : ms' = [⟨.M, W' - 2⟩] := hct
      subst hms'
      obtain ⟨-, -, hwf'⟩ := rounds_run 1000 r _ _ hwf (by rw [hr]; intro h; cases h)
      rw [hr] at hwf'
      have hW' := roundWF_one.mp hwf'
      have hk1 : 0 < k := by
        rcases Nat.eq_zero_or_pos k with rfl | h0
        · simp only [steps, Option.some.injEq] at hk'
          exact absurd hk' (passStart_clean_ne hP hlt)
        · exact h0
      have hkT' : k < T := by
        rcases Nat.lt_or_ge k T with h | h
        · exact h
        · rw [show T - k = 0 by omega] at hT'
          simp [steps] at hT'
      exact ⟨[], a, b, W, R, .nil hP, hh, Or.inr (Or.inr ⟨k, W', hk1, hkT', hlt, hW'.2, hk', hT'⟩)⟩

#print axioms passCutC_iff_of
#print axioms pass_next_close
#print axioms pass_halt_chain_close

end BB6
