import LoopHalt
import BB6.PassTree
import BB6.CleanTree

/-!
# A halt from a pass start: the pass-start trees

`loop_chain_halt` follows a halting run from a pass start through the loop's chain to its end; where the chain ends,
it only says that a stuck configuration follows.  The pass-start trees (`BB6/PassTree.lean`) follow the run further:
from a pass start to the next *checkpoint*, a landing of the chain reached with every end meeting on the way at
distance at least 3, or a one-marker clean tape wider than the start (`pass_next`), unless the left countdown is in the
closing class or the start lies in a cut leaf of its tree.  An end meeting at distance 2 does not stop a tree where
the round model goes on from it to a new round start.  There is one tree for each right end R < 178 (`passTreeR`) and
one for every R ≥ 178, with R a coordinate (`passTreeSym`).  The trees are built by the proved explorer
(`PTree.explore_ok`), so `pass_next` holds at every depth d with nothing evaluated.  Where the cone's edge leaves a
round undecided, the explorer cleaves the class (`cleave`, at most `passCleaves` times on a path): the slice of its
smallest members in one coordinate goes on with one coordinate less, the rest under a tighter cone.

`pass_halt_chain` chains the checkpoints by induction on the halting time, from a pass start of width at least 2¹³
with every gap at least 448 (and, if W ≡ 2 mod 4, the middle wall at least 896 from the end): every landing on the way
is again such a pass start (`landing_wide`), so the run follows the loop's chain (`LoopChain`) to a last pass start,
where R is in the closing set with the left countdown in R's class, and a stuck configuration follows; or the last
pass start lies in a cut leaf of its tree at every depth; or the run reaches a wider clean tape, from which it halts
in fewer steps.
-/

namespace BB6
open BB6.Sym

/-- The cleaves the explorer may make on a path. -/
def passCleaves : Nat := 8

/-- The pass-start tree for the pass starts with right end R < 178 (the class `startR R`), `d` splits deep. -/
def passTreeR (R d : Nat) : PTree :=
  PTree.explore 448 1000 3 (closeClass R) (10000 + d) d passCleaves false true 0 (startR R).1 (startR R).2.1
    (startR R).2.2 (startE R).2

/-- The pass-start tree for the pass starts with right end R ≥ 178 (the class `symStart`), `d` splits deep. -/
def passTreeSym (d : Nat) : PTree :=
  PTree.explore 448 1000 4 none (10000 + d) d passCleaves false true 0 symStart.1 symStart.2.1 symStart.2.2
    symStartE.2

theorem passTreeR_ok (R d : Nat) :
    (passTreeR R d).ok 448 1000 3 (closeClass R) false true 0 (startR R).1 (startR R).2.1 (startR R).2.2
      (startE R).2 = true :=
  PTree.explore_ok 448 1000 3 (closeClass R) (10000 + d) d passCleaves false true 0 (startR R).1 (startR R).2.1
    (startR R).2.2 (startE R).2

theorem passTreeSym_ok (d : Nat) :
    (passTreeSym d).ok 448 1000 4 none false true 0 symStart.1 symStart.2.1 symStart.2.2 symStartE.2 = true :=
  PTree.explore_ok 448 1000 4 none (10000 + d) d passCleaves false true 0 symStart.1 symStart.2.1 symStart.2.2
    symStartE.2

/-- The pass start with walls at a, b and W − R − 1, width W and right end R lies in a cut leaf of its pass-start
tree `d` splits deep (at the point ((a − 1)/2, b/2, W/2), and R/2 for R ≥ 178). -/
def PassCut (d R a b W : Nat) : Prop :=
  if R < 178 then (passTreeR R d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W : Int) / 2] = true
  else (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W : Int) / 2, (R : Int) / 2] = true

/-- **From a pass start to the next checkpoint.**  For every depth d and every phase-0 pass start with right end R and
every gap at least 448: either R is in the closing set and the left countdown is in R's class (`InCloseClass`); or
the start lies in a cut leaf of its pass-start tree d splits deep (`PassCut`); or the machine runs r rounds without
halting, to a landing of the loop's chain (`Landing`, with the step's exact map) with every end meeting on the way at
distance at least 3 (no close), or, after at least one round, to a one-marker clean tape wider than the start. -/
theorem pass_next (d R a b W : Nat) (hP : PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R) :
    InCloseClass [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R ∨ PassCut d R a b W ∨
    ∃ r kk ms' W', steps kk (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = some (roundStart ms' W') ∧
      roundsZ 1000 r [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W = .newRound ms' W' ∧
      (((∀ e ∈ meetsRounds 1000 r [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W, 3 ≤ e) ∧
          Landing r W R (passL1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) ms' W') ∨
        (0 < r ∧ CleanTape ms' W' ∧ W < W')) := by
  obtain ⟨a₀, b₀, hms, ha, hb, hE, hR, hR2, h1, h2, h3⟩ := hP
  simp only [List.cons.injEq, Mark.mk.injEq, true_and, and_true] at hms
  obtain ⟨rfl, rfl⟩ := hms
  by_cases hR178 : 178 ≤ R
  · -- the tree for every R ≥ 178, at the point (a, b, W, R)
    let y : List Int := [((a : Int) - 1) / 2, (b : Int) / 2, (W : Int) / 2, (R : Int) / 2]
    have hy : inCone symStart.2.2 448 y := by
      intro f hf
      simp only [symStart, List.mem_cons, List.mem_nil_iff, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl <;>
        simp only [y, YForm.eval, YForm.sub, YForm.add, YForm.neg, YForm.addc, addL, smulL, List.map, dot] <;> omega
    have hs : agL y symStart.1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] := by
      refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, trivial⟩ <;>
        simp only [agN, y, YForm.eval, YForm.sub, YForm.add, YForm.neg, YForm.addc, addL, smulL, List.map, dot] <;>
        omega
    have hW : agN y symStart.2.1 W := by simp only [agN, y, symStart, YForm.eval, dot]; omega
    have hf : symStartE.2.Ag y W R (loopL1 b (W - R - 1) W) := by
      refine ⟨?_, ?_, ?_⟩
      · simp only [agN, y, symStartE, YForm.eval, dot]; omega
      · simp only [agN, y, symStartE, YForm.eval, dot]; omega
      · simp only [symStartE, eval_L1Form, loopL1]
        simp only [y, YForm.eval, YForm.sub, YForm.add, YForm.neg, YForm.addc, addL, smulL, List.map, dot]
        omega
    rcases PTree.sound 448 1000 4 none (passTreeSym d) false true 0 symStart.1 symStart.2.1 symStart.2.2
        symStartE.2 (passTreeSym_ok d) y rfl hy _ W W R _ hs hW hf (fun h => by cases h) with
      hc | ⟨_, _, h, -⟩ | ⟨r, kk, ms', W', hk, hr, hev⟩
    · right; left
      simp only [PassCut, show ¬ R < 178 by omega, ↓reduceIte]
      exact hc
    · cases h
    · right; right
      refine ⟨r, kk, ms', W', hk, hr, ?_⟩
      rcases hev with ⟨-, hm, hl⟩ | ⟨h0, hc, hlt⟩
      · simp only [Nat.zero_add] at hl
        exact Or.inl ⟨hm, hl⟩
      · exact Or.inr ⟨by omega, hc, hlt⟩
  · -- the tree for R
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
    rcases PTree.sound 448 1000 3 (closeClass R) (passTreeR R d) false true 0 (startR R).1 (startR R).2.1
        (startR R).2.2 (startE R).2 (passTreeR_ok R d) y rfl hy _ W W R _ hs hW hf (fun h => by cases h) with
      hc | ⟨m, c, hm, hl⟩ | ⟨r, kk, ms', W', hk, hr, hev⟩
    · right; left
      simp only [PassCut, show R < 178 by omega, ↓reduceIte]
      exact hc
    · left
      exact ⟨a, b, m, c, rfl, hm, hl⟩
    · right; right
      refine ⟨r, kk, ms', W', hk, hr, ?_⟩
      rcases hev with ⟨-, hm, hl⟩ | ⟨h0, hc, hlt⟩
      · simp only [Nat.zero_add] at hl
        exact Or.inl ⟨hm, hl⟩
      · exact Or.inr ⟨by omega, hc, hlt⟩

/-- A pass start is not a wider one-marker clean tape. -/
theorem passStart_clean_ne {ms : List Mark} {W R W' : Nat} (hP : PassStart448 ms W R) (hlt : W < W') :
    roundStart ms W ≠ roundStart [⟨.M, W' - 2⟩] W' := by
  obtain ⟨a, b, rfl, -, -, -, -, hR2, h1, h2, h3⟩ := hP
  intro h
  have hr := congrArg (fun c => c.r (W' - 5 + 1)) h
  simp only [roundStart, cons] at hr
  rw [clean_cell W' (by omega), show W' - 5 = W - 4 + (W' - W - 1) by omega,
    www_blank a b (W - R - 1) W (by omega) (by omega) (by omega) (by omega)] at hr
  cases hr

/-- **A halt from a wide pass start: the checkpoints.**  If the machine halts T steps after a phase-0 pass start of
width W ≥ 2¹³ with right end R and every gap at least 448 (and, if W ≡ 2 mod 4, the middle wall b at least 896 from
the end), then its run from there follows the loop's chain (`LoopChain`), each step close-free with its exact map, to a
last pass start with walls a₁, b₁, W₁ − R₁ − 1, again with every gap at least 448 (and the middle wall at least 896 from
the end if W₁ ≡ 2 mod 4), where: R₁ is in the closing set and the left countdown is in R₁'s class (`InCloseClass`),
and the mark model, run on from there, reaches a stuck configuration; or the last pass start lies in a cut leaf of its
pass-start tree at every depth (`PassCut`); or the run, from the last pass start, reaches a one-marker clean tape of
even width W′ > W after k steps, 0 < k < T, and halts T − k steps after it. -/
theorem pass_halt_chain (T : Nat) : ∀ (R a b W : Nat), PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R →
    2 ^ 13 ≤ W → (W % 4 = 2 → b + 896 ≤ W) →
    steps T (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = none →
    ∃ ks a₁ b₁ W₁ R₁,
      LoopChain [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R ks [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁ R₁ ∧
      (W₁ % 4 = 2 → b₁ + 896 ≤ W₁) ∧
      ((InCloseClass [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁ R₁ ∧
          ∃ t, Reach ⟨[], 1, [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩], W₁⟩ t ∧ t.wf ∧
            (EndClose t ∨ InteriorContact t)) ∨
        (∀ d, PassCut d R₁ a₁ b₁ W₁) ∨
        ∃ k W', 0 < k ∧ k < T ∧ W < W' ∧ W' % 2 = 0 ∧
          steps k (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = some (roundStart [⟨.M, W' - 2⟩] W') ∧
          steps (T - k) (roundStart [⟨.M, W' - 2⟩] W') = none) := by
  induction T using Nat.strongRecOn with
  | ind T ih =>
    intro R a b W hP hW hh hT
    obtain ⟨hwf, hG⟩ := hP.wf
    by_cases hc : InCloseClass [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R
    · obtain ⟨t, ht, htw, hts⟩ := round_halt_needs_contact _ W T hwf hG hT
      exact ⟨[], a, b, W, R, .nil hP, hh, Or.inl ⟨hc, t, ht, htw, stuck_cases hts⟩⟩
    by_cases hcut : ∀ d, PassCut d R a b W
    · exact ⟨[], a, b, W, R, .nil hP, hh, Or.inr (Or.inl hcut)⟩
    obtain ⟨d, hd⟩ := Classical.not_forall.mp hcut
    rcases pass_next d R a b W hP with hc' | hd' | ⟨r, kk, ms', W', hk, hr, hev⟩
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

#print axioms pass_next
#print axioms pass_halt_chain

end BB6
