import ExitPieces0
import ExitPieces1
import ExitPieces2
import ExitPieces3
import BB6.Meets
open BB6 BB6.Sym

/-! # The exit certificate as a theorem

The tree below was built by the untrusted program `ExploreExit.lean` (coordinate splits and skews, so it covers the
start class by construction; `adv` nodes run the rounds before a split once for the whole subtree) and is checked by
the proved function `Tree.ok`, evaluated by the kernel (`decide +kernel`; no compiler is trusted).  The check is cut
into subtrees `exitP0`, `exitP1`, … with a theorem each (one kernel evaluation of the whole check would hold too many
terms in memory), in the modules `ExitPieces0`, … (compiled in parallel), and assembled here into `exit_tree_ok` by
`Tree.ok_node` and `Tree.ok_skew`.  `exit_no_halt` is the statement for the machine. -/

def exitTree : Tree := (.skew 2 3 1 (.node 2 (.skew 1 3 1 (.node 1 (.node 3 (.node 2 exitP0 exitP1) (.node 2 (.skew 1 3 1 (.node 1 (.node 2 exitP2 exitP3) exitP4)) exitP5)) (.node 1 (.node 3 (.skew 2 3 1 (.node 2 exitP6 (.node 3 exitP7 exitP8))) exitP9) exitP10))) (.skew 1 3 1 (.node 1 exitP11 (.node 3 (.skew 1 3 1 (.node 1 exitP12 (.node 2 (.skew 1 3 1 (.node 1 (.node 2 exitP13 exitP14) (.node 1 exitP15 (.skew 2 3 1 (.node 2 exitP16 (.node 3 exitP17 exitP18)))))) (.skew 1 3 1 (.node 1 exitP19 (.skew 1 3 1 (.node 1 exitP20 (.node 2 (.skew 1 3 1 (.node 1 exitP21 (.node 2 (.skew 1 3 1 (.node 1 exitP22 exitP23)) (.skew 1 3 1 (.node 1 exitP24 exitP25))))) (.skew 1 3 1 (.node 1 (.node 2 (.node 1 (.node 2 (.skew 1 3 1 (.node 1 exitP26 (.node 2 exitP27 exitP28))) (.skew 1 3 1 (.node 1 exitP29 exitP30))) exitP31) exitP32) exitP33)))))))))) (.node 2 (.node 1 (.skew 1 2 1 (.node 1 (.skew 2 3 1 (.node 2 exitP34 (.node 3 exitP35 exitP36))) exitP37)) (.node 2 exitP38 (.skew 1 2 1 (.node 1 exitP39 exitP40)))) (.node 1 exitP41 (.skew 1 2 1 (.skew 1 3 1 (.node 1 (.node 2 (.skew 1 3 1 (.node 1 (.skew 1 2 1 (.node 1 exitP42 (.skew 2 3 1 (.node 2 exitP43 (.node 3 exitP44 exitP45))))) (.node 2 exitP46 exitP47))) (.skew 1 3 1 (.node 1 exitP48 (.skew 1 2 1 (.skew 1 3 1 (.node 1 (.node 2 (.skew 1 3 1 (.node 1 exitP49 (.node 2 (.skew 1 3 1 (.node 1 exitP50 exitP51)) (.skew 1 3 1 (.node 1 exitP52 exitP53))))) exitP54) exitP55)))))) exitP56))))))))))

theorem exit_tree_ok : exitTree.ok 390 1000 4 false exitStart.1 exitStart.2.1 exitStart.2.2 = true :=
  (Tree.ok_skew (by decide) (by decide) (by decide) (Tree.ok_node (by decide) (Tree.ok_skew (by decide) (by decide) (by decide) (Tree.ok_node (by decide) (Tree.ok_node (by decide) (Tree.ok_node (by decide) exitP0_ok exitP1_ok) (Tree.ok_node (by decide) (Tree.ok_skew (by decide) (by decide) (by decide) (Tree.ok_node (by decide) (Tree.ok_node (by decide) exitP2_ok exitP3_ok) exitP4_ok)) exitP5_ok)) (Tree.ok_node (by decide) (Tree.ok_node (by decide) (Tree.ok_skew (by decide) (by decide) (by decide) (Tree.ok_node (by decide) exitP6_ok (Tree.ok_node (by decide) exitP7_ok exitP8_ok))) exitP9_ok) exitP10_ok))) (Tree.ok_skew (by decide) (by decide) (by decide) (Tree.ok_node (by decide) exitP11_ok (Tree.ok_node (by decide) (Tree.ok_skew (by decide) (by decide) (by decide) (Tree.ok_node (by decide) exitP12_ok (Tree.ok_node (by decide) (Tree.ok_skew (by decide) (by decide) (by decide) (Tree.ok_node (by decide) (Tree.ok_node (by decide) exitP13_ok exitP14_ok) (Tree.ok_node (by decide) exitP15_ok (Tree.ok_skew (by decide) (by decide) (by decide) (Tree.ok_node (by decide) exitP16_ok (Tree.ok_node (by decide) exitP17_ok exitP18_ok)))))) (Tree.ok_skew (by decide) (by decide) (by decide) (Tree.ok_node (by decide) exitP19_ok (Tree.ok_skew (by decide) (by decide) (by decide) (Tree.ok_node (by decide) exitP20_ok (Tree.ok_node (by decide) (Tree.ok_skew (by decide) (by decide) (by decide) (Tree.ok_node (by decide) exitP21_ok (Tree.ok_node (by decide) (Tree.ok_skew (by decide) (by decide) (by decide) (Tree.ok_node (by decide) exitP22_ok exitP23_ok)) (Tree.ok_skew (by decide) (by decide) (by decide) (Tree.ok_node (by decide) exitP24_ok exitP25_ok))))) (Tree.ok_skew (by decide) (by decide) (by decide) (Tree.ok_node (by decide) (Tree.ok_node (by decide) (Tree.ok_node (by decide) (Tree.ok_node (by decide) (Tree.ok_skew (by decide) (by decide) (by decide) (Tree.ok_node (by decide) exitP26_ok (Tree.ok_node (by decide) exitP27_ok exitP28_ok))) (Tree.ok_skew (by decide) (by decide) (by decide) (Tree.ok_node (by decide) exitP29_ok exitP30_ok))) exitP31_ok) exitP32_ok) exitP33_ok)))))))))) (Tree.ok_node (by decide) (Tree.ok_node (by decide) (Tree.ok_skew (by decide) (by decide) (by decide) (Tree.ok_node (by decide) (Tree.ok_skew (by decide) (by decide) (by decide) (Tree.ok_node (by decide) exitP34_ok (Tree.ok_node (by decide) exitP35_ok exitP36_ok))) exitP37_ok)) (Tree.ok_node (by decide) exitP38_ok (Tree.ok_skew (by decide) (by decide) (by decide) (Tree.ok_node (by decide) exitP39_ok exitP40_ok)))) (Tree.ok_node (by decide) exitP41_ok (Tree.ok_skew (by decide) (by decide) (by decide) (Tree.ok_skew (by decide) (by decide) (by decide) (Tree.ok_node (by decide) (Tree.ok_node (by decide) (Tree.ok_skew (by decide) (by decide) (by decide) (Tree.ok_node (by decide) (Tree.ok_skew (by decide) (by decide) (by decide) (Tree.ok_node (by decide) exitP42_ok (Tree.ok_skew (by decide) (by decide) (by decide) (Tree.ok_node (by decide) exitP43_ok (Tree.ok_node (by decide) exitP44_ok exitP45_ok))))) (Tree.ok_node (by decide) exitP46_ok exitP47_ok))) (Tree.ok_skew (by decide) (by decide) (by decide) (Tree.ok_node (by decide) exitP48_ok (Tree.ok_skew (by decide) (by decide) (by decide) (Tree.ok_skew (by decide) (by decide) (by decide) (Tree.ok_node (by decide) (Tree.ok_node (by decide) (Tree.ok_skew (by decide) (by decide) (by decide) (Tree.ok_node (by decide) exitP49_ok (Tree.ok_node (by decide) (Tree.ok_skew (by decide) (by decide) (by decide) (Tree.ok_node (by decide) exitP50_ok exitP51_ok)) (Tree.ok_skew (by decide) (by decide) (by decide) (Tree.ok_node (by decide) exitP52_ok exitP53_ok))))) exitP54_ok) exitP55_ok)))))) exitP56_ok))))))))))

/-- **From any loop state with large gaps, the machine runs on without halting.**  For all naturals a, b, c, E with
a odd, b even, c odd, E even and every gap at least 390 (a ≥ 390, b − a ≥ 390, c − b ≥ 390, E − c ≥ 390), the machine
started from the round start with walls at a, b, c and width E reaches, after some number n of rounds (the round at
which this state's run breaks off, cleans the tape or completes a pass, per the tree), another round start; it does
not halt on the way. -/
theorem exit_no_halt (a b c E : Nat) (ha : a % 2 = 1) (hb : b % 2 = 0) (hc : c % 2 = 1) (hE : E % 2 = 0)
    (h1 : 390 ≤ a) (h2 : a + 390 ≤ b) (h3 : b + 390 ≤ c) (h4 : c + 390 ≤ E) :
    ∃ n kk ms' W', steps kk (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E) = some (roundStart ms' W') ∧
      roundsZ 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E = .newRound ms' W' := by
  let y : List Int := [((a : Int) - 1) / 2, (b : Int) / 2, ((c : Int) - 1) / 2, (E : Int) / 2]
  have hy : inCone exitStart.2.2 390 y := by
    intro t ht
    simp only [exitStart, List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl <;>
      simp only [y, YForm.eval, YForm.sub, YForm.add, YForm.neg, addL, smulL, List.map, dot] <;> omega
  have hs : agL y exitStart.1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] := by
    refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, trivial⟩ <;>
      simp only [agN, y, YForm.eval, dot] <;> omega
  have hW : agN y exitStart.2.1 E := by simp only [agN, y, exitStart, YForm.eval, dot]; omega
  exact Tree.sound 390 1000 4 exitTree false _ _ _ exit_tree_ok y rfl hy _ _ hs hW (fun h => by cases h)
