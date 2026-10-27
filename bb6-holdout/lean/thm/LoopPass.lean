import LoopPieces0
import LoopPieces1
import LoopPieces2
import LoopPieces3
open BB6 BB6.Sym

/-! # One stretch of the loop with the right end free

The phase-0 pass starts with R ≥ 4097 form one class (`loopStart`).  One tree of coordinate splits and skews (built by
the untrusted program `ExploreLoop.lean`, so it covers the class by construction; `adv` nodes run the rounds before a
split once for the whole subtree) is checked by the proved function `Tree.okLoop`, evaluated by the kernel
(`decide +kernel`; no compiler is trusted).  The check is cut into subtrees `loopP0`, `loopP1`, … with a theorem each,
in the modules `LoopPieces0`, … (compiled in parallel), and assembled here into `loop_tree_ok` by `Tree.okLoop_node`
and `Tree.okLoop_skew`.  `loop_pass` is the statement for the machine. -/

def loopTree : Tree := (.node 3 (.skew 1 2 1 (.node 1 loopP0 (.node 2 (.skew 1 2 1 (.node 1 loopP1 (.node 3 (.skew 1 2 1 (.node 1 loopP2 (.skew 1 2 1 (.node 1 loopP3 (.node 3 (.skew 1 2 1 (.node 1 (.node 3 loopP4 (.node 1 (.node 3 (.skew 1 2 1 (.node 1 loopP5 loopP6)) (.skew 1 2 1 (.node 1 loopP7 (.node 3 loopP8 loopP9)))) loopP10)) loopP11)) (.skew 1 2 1 (.node 1 loopP12 (.node 3 (.skew 1 2 1 (.node 1 loopP13 loopP14)) (.skew 1 2 1 (.node 1 loopP15 loopP16)))))))))) (.skew 1 2 1 (.node 1 (.node 3 loopP17 loopP18) (.node 1 loopP19 (.skew 2 3 1 (.node 2 (.node 3 loopP20 loopP21) loopP22)))))))) loopP23))) loopP24)

theorem loop_tree_ok :
    loopTree.okLoop 448 1000 4 false loopLS.1.1 loopLS.1.2.1 loopLS.1.2.2 loopLS.2.1 loopLS.2.2 = true :=
  (Tree.okLoop_node (by decide) (Tree.okLoop_skew (by decide) (by decide) (by decide) (Tree.okLoop_node (by decide) loopP0_ok (Tree.okLoop_node (by decide) (Tree.okLoop_skew (by decide) (by decide) (by decide) (Tree.okLoop_node (by decide) loopP1_ok (Tree.okLoop_node (by decide) (Tree.okLoop_skew (by decide) (by decide) (by decide) (Tree.okLoop_node (by decide) loopP2_ok (Tree.okLoop_skew (by decide) (by decide) (by decide) (Tree.okLoop_node (by decide) loopP3_ok (Tree.okLoop_node (by decide) (Tree.okLoop_skew (by decide) (by decide) (by decide) (Tree.okLoop_node (by decide) (Tree.okLoop_node (by decide) loopP4_ok (Tree.okLoop_node (by decide) (Tree.okLoop_node (by decide) (Tree.okLoop_skew (by decide) (by decide) (by decide) (Tree.okLoop_node (by decide) loopP5_ok loopP6_ok)) (Tree.okLoop_skew (by decide) (by decide) (by decide) (Tree.okLoop_node (by decide) loopP7_ok (Tree.okLoop_node (by decide) loopP8_ok loopP9_ok)))) loopP10_ok)) loopP11_ok)) (Tree.okLoop_skew (by decide) (by decide) (by decide) (Tree.okLoop_node (by decide) loopP12_ok (Tree.okLoop_node (by decide) (Tree.okLoop_skew (by decide) (by decide) (by decide) (Tree.okLoop_node (by decide) loopP13_ok loopP14_ok)) (Tree.okLoop_skew (by decide) (by decide) (by decide) (Tree.okLoop_node (by decide) loopP15_ok loopP16_ok)))))))))) (Tree.okLoop_skew (by decide) (by decide) (by decide) (Tree.okLoop_node (by decide) (Tree.okLoop_node (by decide) loopP17_ok loopP18_ok) (Tree.okLoop_node (by decide) loopP19_ok (Tree.okLoop_skew (by decide) (by decide) (by decide) (Tree.okLoop_node (by decide) (Tree.okLoop_node (by decide) loopP20_ok loopP21_ok) loopP22_ok)))))))) loopP23_ok))) loopP24_ok)

/-- **One stretch of the loop, for every width.**  For every phase-0 pass start with right end R ≥ 4097 — walls at
a, b and c = E − R − 1, width E, with a odd, b even, E even, R even and every gap at least 448 — the machine runs a
number of rounds without halting and without a close (every end meeting at distance ≥ 3), and the round start it
reaches is either not a phase-0 pass start, or a phase-0 pass start with every gap at least 448 and a smaller even
right end R′ > 176: a full pass, R′ = R/16 with left countdown L₁′ = L₁/64, or R′ = R/2. -/
theorem loop_pass (R a b E : Nat) (hR : R % 2 = 0) (hR4 : 4097 ≤ R) (ha : a % 2 = 1) (hb : b % 2 = 0)
    (hE : E % 2 = 0) (h1 : 448 ≤ a) (h2 : a + 448 ≤ b) (h3 : b + 448 + R + 1 ≤ E) :
    ∃ n kk ms' W', steps kk (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E) = some (roundStart ms' W') ∧
      roundsZ 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E = .newRound ms' W' ∧
      (∀ d ∈ meetsRounds 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E, 3 ≤ d) ∧
      LoopOut R (loopL1 b (E - R - 1) E) ms' W' := by
  let y : List Int := [((a : Int) - 1) / 2, (b : Int) / 2, (E : Int) / 2, (R : Int) / 2]
  have hy : inCone loopStart.2.2 448 y := by
    intro f hf
    simp only [loopStart, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl <;>
      simp only [y, YForm.eval, YForm.sub, YForm.add, YForm.neg, YForm.addc, addL, smulL, List.map, dot] <;> omega
  have hs : agL y loopStart.1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] := by
    refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, trivial⟩ <;>
      simp only [agN, y, YForm.eval, YForm.sub, YForm.add, YForm.neg, YForm.addc, addL, smulL, List.map, dot] <;>
      omega
  have hW : agN y loopStart.2.1 E := by simp only [agN, y, loopStart, YForm.eval, dot]; omega
  have hRa : agN y loopR R := by simp only [agN, y, loopR, YForm.eval, dot]; omega
  have hL : loopL1 b (E - R - 1) E = loopL.eval y := by
    simp only [loopL, eval_L1Form, loopL1]
    simp only [y, YForm.eval, YForm.sub, YForm.add, YForm.neg, YForm.addc, addL, smulL, List.map, dot]
    omega
  exact Tree.soundLoop 448 1000 4 loopTree false _ _ _ _ _ loop_tree_ok y rfl hy _ E R _ hs hW hRa hL
    (fun h => by cases h)
