import PassHalt
import BB6.HaltTree

/-!
# Pass starts that halt: the halting classes

The model's close at the right end with the end marker at distance 0 (`EndClose0`) is a halt, and so is every
configuration from which the model reaches it (`reach_close_halt`, `BB6/CloseHalt.lean`).  The close run on symbolic
positions (`symCloseRun`) follows the model on a whole class of round starts, across rounds, to that close, so a class
it closes halts, member by member (`symCloseRun_halt`).  Two uses of it on the pass starts:

* `pass_halt_leaf`: the halting tree read off a pass-start tree (`HTree.ofPTree`, `BB6/HaltTree.lean`) marks the close
  and cut leaves whose class the close run closes; every pass start in such a leaf halts, at every depth, with nothing
  evaluated.
* `pass_class_halt`: at 12 and 16 splits those leaves are the classes of `HaltClass`, and at 20 splits they have the
  same measure (`PassStats.lean`, untrusted): all of the pass starts with R = 2, 3/8 of those with R = 4, 1/8 of those
  with R = 6 (`pass_r6_halt`), and 1/32, 1/64, 1/128 and 1/256 of those with R = 8, 16, 32 and 48, by residues of the
  middle wall b and the width W; none for the other R < 178.  Apart from R = 6's, they are exactly the close leaves.
  Each class halts: the close run on the class is evaluated by the kernel (`decide +kernel`).

`chain_class_halt`: a pass start whose loop chain (`LoopChain`) reaches a pass start in one of the classes halts.  In
600,000 random pass starts with R < 178 (widths 2¹² to 2³⁰), the model's run ends at a one-marker clean tape (98.1%)
or at this close (1.9%), and every run that ends at the close passes through a pass start in one of the classes.  Past
the end of the loop's chain, the run can still reach a class by entering the loop again, through an end meeting off
the chain whose own halving chain runs to 0 (`pass_halt_example_reentry`; three of twelve million sampled starts with
R from 50 to 176, at width 2¹², and none of ten million with R ≥ 178).
-/

namespace BB6
open BB6.Sym

/-- The events the close run may take. -/
def closeFuel : Nat := 3000

/-! ## The halting trees -/

/-- The halting tree of the pass-start tree for the pass starts with right end R (`passTreeR`), `d` splits deep. -/
def haltTreeR (R d : Nat) : HTree :=
  HTree.ofPTree 448 closeFuel 3 (passTreeR R d) (startR R).1 (startR R).2.1 (startR R).2.2

/-- The pass start with walls at a, b and W − R − 1 and width W lies in a halting leaf of its halting tree `d` splits
deep (at the point ((a − 1)/2, b/2, W/2)). -/
def PassHaltLeaf (d R a b W : Nat) : Prop :=
  (haltTreeR R d).haltMem [((a : Int) - 1) / 2, (b : Int) / 2, (W : Int) / 2] = true

/-- **The halting leaves halt.**  For every depth d, every phase-0 pass start with every gap at least 448 that lies in
a halting leaf of its halting tree halts. -/
theorem pass_halt_leaf (d R a b W : Nat) (hP : PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R)
    (hm : PassHaltLeaf d R a b W) : ∃ T, steps T (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = none := by
  obtain ⟨hwf, hG⟩ := hP.wf
  obtain ⟨a₀, b₀, hms, ha, hb, hE, hR, hR2, h1, h2, h3⟩ := hP
  simp only [List.cons.injEq, Mark.mk.injEq, true_and, and_true] at hms
  obtain ⟨rfl, rfl⟩ := hms
  have hy : inCone (startR R).2.2 448 [((a : Int) - 1) / 2, (b : Int) / 2, (W : Int) / 2] := by
    intro f hf
    simp only [startR, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl <;>
      simp only [YForm.eval, YForm.sub, YForm.add, YForm.neg, YForm.addc, addL, smulL, List.map, dot] <;> omega
  have hs : agL [((a : Int) - 1) / 2, (b : Int) / 2, (W : Int) / 2] (startR R).1
      [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] := by
    refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, trivial⟩ <;> simp only [agN, YForm.eval, YForm.addc, dot] <;> omega
  have hW : agN [((a : Int) - 1) / 2, (b : Int) / 2, (W : Int) / 2] (startR R).2.1 W := by
    simp only [agN, startR, YForm.eval, dot]; omega
  exact HTree.sound 448 closeFuel 3 _ _ _ _ (HTree.ofPTree_ok 448 closeFuel 3 _ _ _ _) _ rfl hy _ W hs hW hwf hG hm

/-! ## The halting classes -/

/-- A class of pass starts with right end R: walls at a = 2 z₀ + 1, b = `bF` and c = W − R − 1, width W = `WF`, with
the cone gaps a, b − a and c − b. -/
def passClass (R : Nat) (bF WF : YForm) : List SMark × YForm × List YForm :=
  let a : YForm := ⟨1, [2, 0, 0]⟩
  let c := WF.addc (-(R : Int) - 1)
  ([⟨.W, a⟩, ⟨.W, bF⟩, ⟨.W, c⟩], WF, [a, bF.sub a, c.sub bF])

/-- The close run on a class, from its round start. -/
def classCheck (R : Nat) (bF WF : YForm) : Bool :=
  symCloseRun (passClass R bF WF).2.2 448 closeFuel [] (YForm.const 1) (passClass R bF WF).1 (passClass R bF WF).2.1

/-- **A class that the close run closes halts**: every phase-0 pass start with every gap at least 448 whose middle
wall and width are the class's forms at some point halts. -/
theorem passClass_halt {R : Nat} {bF WF : YForm} (hc : classCheck R bF WF = true) {a b W : Nat}
    (hP : PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R) (z₁ z₂ : Int)
    (hb : (b : Int) = bF.eval [((a : Int) - 1) / 2, z₁, z₂]) (hW : (W : Int) = WF.eval [((a : Int) - 1) / 2, z₁, z₂]) :
    ∃ T, steps T (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = none := by
  obtain ⟨hwf, hG⟩ := hP.wf
  obtain ⟨a₀, b₀, hms, ha, -, -, -, -, h1, h2, h3⟩ := hP
  simp only [List.cons.injEq, Mark.mk.injEq, true_and, and_true] at hms
  obtain ⟨rfl, rfl⟩ := hms
  have hA : YForm.eval ⟨1, [2, 0, 0]⟩ [((a : Int) - 1) / 2, z₁, z₂] = a := by
    simp only [YForm.eval, dot]; omega
  have hy : inCone (passClass R bF WF).2.2 448 [((a : Int) - 1) / 2, z₁, z₂] := by
    intro f hf
    simp only [passClass, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl <;> simp only [eval_sub, eval_addc, hA, ← hb, ← hW] <;> omega
  have hs : agL [((a : Int) - 1) / 2, z₁, z₂] (passClass R bF WF).1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] := by
    refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, trivial⟩ <;> simp only [agN, eval_addc, hA, ← hb, ← hW] <;> omega
  exact symCloseRun_halt _ _ closeFuel hc hy hs hW hwf hG

/-- The halting classes of the phase-0 pass starts, by right end R, middle wall b and width W. -/
def HaltClass (R b W : Nat) : Prop :=
  R = 2 ∨
  R = 4 ∧ (W % 4 = 0 ∧ b % 8 = 6 ∨ W % 4 = 2 ∧ b % 4 = 0) ∨
  R = 6 ∧ W % 4 = 2 ∧ b % 8 = 2 ∨
  R = 8 ∧ W % 4 = 0 ∧ b % 32 = 30 ∨
  R = 16 ∧ W % 4 = 0 ∧ b % 64 = 30 ∨
  R = 32 ∧ W % 4 = 0 ∧ b % 128 = (30 + 16 * W) % 128 ∨
  R = 48 ∧ W % 4 = 0 ∧ b % 256 = (158 + 48 * W) % 256

/-- The close run closes each class (in the coordinates z = ((a − 1)/2, z₁, z₂), b = `bF`, W = `WF`). -/
theorem classCheck_2 : classCheck 2 ⟨0, [0, 2, 0]⟩ ⟨0, [0, 0, 2]⟩ = true := by decide +kernel
theorem classCheck_4a : classCheck 4 ⟨6, [0, 8, 0]⟩ ⟨0, [0, 0, 4]⟩ = true := by decide +kernel
theorem classCheck_4b : classCheck 4 ⟨4, [0, 4, 0]⟩ ⟨2, [0, 0, 4]⟩ = true := by decide +kernel
theorem classCheck_6 : classCheck 6 ⟨2, [0, 8, 0]⟩ ⟨2, [0, 0, 4]⟩ = true := by decide +kernel
theorem classCheck_8 : classCheck 8 ⟨30, [0, 32, 0]⟩ ⟨0, [0, 0, 4]⟩ = true := by decide +kernel
theorem classCheck_16 : classCheck 16 ⟨30, [0, 64, 0]⟩ ⟨0, [0, 0, 4]⟩ = true := by decide +kernel
theorem classCheck_32 : classCheck 32 ⟨30, [0, 128, 64]⟩ ⟨0, [0, 0, 4]⟩ = true := by decide +kernel
theorem classCheck_48 : classCheck 48 ⟨158, [0, 256, 192]⟩ ⟨0, [0, 0, 4]⟩ = true := by decide +kernel

/-- **The halting classes halt.**  Every phase-0 pass start with every gap at least 448 in a halting class halts. -/
theorem pass_class_halt (R a b W : Nat) (hP : PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R)
    (h : HaltClass R b W) : ∃ T, steps T (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = none := by
  have hP' := hP
  obtain ⟨a₀, b₀, hms, -, hb, hE, -, -, -, -, -⟩ := hP'
  simp only [List.cons.injEq, Mark.mk.injEq, true_and, and_true] at hms
  obtain ⟨rfl, rfl⟩ := hms
  rcases h with rfl | ⟨rfl, ⟨hW, hb'⟩ | ⟨hW, hb'⟩⟩ | ⟨rfl, hW, hb'⟩ | ⟨rfl, hW, hb'⟩ | ⟨rfl, hW, hb'⟩ | ⟨rfl, hW, hb'⟩ |
    ⟨rfl, hW, hb'⟩
  · exact passClass_halt classCheck_2 hP ((b : Int) / 2) ((W : Int) / 2) (by simp only [YForm.eval, dot]; omega)
      (by simp only [YForm.eval, dot]; omega)
  · exact passClass_halt classCheck_4a hP (((b : Int) - 6) / 8) ((W : Int) / 4) (by simp only [YForm.eval, dot]; omega)
      (by simp only [YForm.eval, dot]; omega)
  · exact passClass_halt classCheck_4b hP (((b : Int) - 4) / 4) (((W : Int) - 2) / 4)
      (by simp only [YForm.eval, dot]; omega) (by simp only [YForm.eval, dot]; omega)
  · exact passClass_halt classCheck_6 hP (((b : Int) - 2) / 8) (((W : Int) - 2) / 4)
      (by simp only [YForm.eval, dot]; omega) (by simp only [YForm.eval, dot]; omega)
  · exact passClass_halt classCheck_8 hP (((b : Int) - 30) / 32) ((W : Int) / 4)
      (by simp only [YForm.eval, dot]; omega) (by simp only [YForm.eval, dot]; omega)
  · exact passClass_halt classCheck_16 hP (((b : Int) - 30) / 64) ((W : Int) / 4)
      (by simp only [YForm.eval, dot]; omega) (by simp only [YForm.eval, dot]; omega)
  · exact passClass_halt classCheck_32 hP (((b : Int) - 30 - 16 * W) / 128) ((W : Int) / 4)
      (by simp only [YForm.eval, dot]; omega) (by simp only [YForm.eval, dot]; omega)
  · exact passClass_halt classCheck_48 hP (((b : Int) - 158 - 48 * W) / 256) ((W : Int) / 4)
      (by simp only [YForm.eval, dot]; omega) (by simp only [YForm.eval, dot]; omega)

/-- The loop's chain is a run of the machine, to a pass start. -/
theorem _root_.LoopChain.reach_last {ms : List Mark} {W R : Nat} {ks : List StepKind} {ms' : List Mark} {W' R' : Nat}
    (h : LoopChain ms W R ks ms' W' R') :
    ∃ t, steps t (roundStart ms W) = some (roundStart ms' W') ∧ PassStart448 ms' W' R' := by
  induction h with
  | nil hP => exact ⟨0, rfl, hP⟩
  | cons _ _ kk _ hk _ _ _ _ _ ih =>
    obtain ⟨t, ht, hP⟩ := ih
    exact ⟨kk + t, steps_seq hk ht, hP⟩

/-- **A chain into a halting class halts.**  A pass start whose loop chain reaches a pass start in a halting class
halts. -/
theorem chain_class_halt {ms : List Mark} {W R : Nat} {ks : List StepKind} {a₁ b₁ W₁ R₁ : Nat}
    (hch : LoopChain ms W R ks [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁ R₁) (h : HaltClass R₁ b₁ W₁) :
    ∃ T, steps T (roundStart ms W) = none := by
  obtain ⟨t, ht, hP⟩ := hch.reach_last
  obtain ⟨T, hT⟩ := pass_class_halt R₁ a₁ b₁ W₁ hP h
  exact ⟨t + T, steps_seq_none ht hT⟩

/-! ## Examples -/

/-- The pass start with walls at 731, 1,886 and 5,603 and width 5,652 (R = 48) is in a halting class (the machine halts
after 72,326,041 steps from it, by the simulators). -/
theorem pass_class_halt_example :
    ∃ T, steps T (roundStart [⟨.W, 731⟩, ⟨.W, 1886⟩, ⟨.W, 5603⟩] 5652) = none :=
  pass_class_halt 48 731 1886 5652 ⟨731, 1886, rfl, by decide⟩ (by unfold HaltClass; decide)

/-- Outside the classes: the pass start with walls at 1,561, 2,440 and 5,033 and width 5,042 (R = 8) reaches one
after two rounds (walls at 1,225, 3,742 and 5,043, width 5,048, R = 4) and halts after 19,785,426 steps, by the
simulators; here the close run on the concrete start, evaluated by the kernel. -/
theorem pass_halt_example_r8 : ∃ T, steps T (roundStart [⟨.W, 1561⟩, ⟨.W, 2440⟩, ⟨.W, 5033⟩] 5042) = none :=
  closeRun_sound closeFuel _ _ (by simp [roundWF, rightOK, mval, mlen])
    (by intro m hm; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm; rcases hm with rfl | rfl | rfl <;> simp)
    (by decide +kernel)

/-- A pass start with R = 256 that halts: walls at 786,501, 1,023,966 and 1,073,891, width 1,074,148; its run lands
at R = 32 after six rounds and at R = 16, in a halting class, after eight. -/
theorem pass_halt_example_r256 :
    ∃ T, steps T (roundStart [⟨.W, 786501⟩, ⟨.W, 1023966⟩, ⟨.W, 1073891⟩] 1074148) = none :=
  closeRun_sound closeFuel _ _ (by simp [roundWF, rightOK, mval, mlen])
    (by intro m hm; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm; rcases hm with rfl | rfl | rfl <;> simp)
    (by decide +kernel)

/-- Past the chain's end: from the pass start with walls at 645, 4,862 and 5,789 and width 5,920 (R = 130) the
chain breaks in round 2 (end meetings at 128, then 332) and no landing follows, but in round 3 the end is met at
254 = 2⁸ − 2, off the old chain, and that meeting's own halving chain (254, 126, …, 2, 0) runs through a pass start
in a halting class (walls at 1,487, 4,446 and 5,939, width 5,956, R = 16, after 11 rounds) to the close. -/
theorem pass_halt_example_reentry :
    ∃ T, steps T (roundStart [⟨.W, 645⟩, ⟨.W, 4862⟩, ⟨.W, 5789⟩] 5920) = none :=
  closeRun_sound closeFuel _ _ (by simp [roundWF, rightOK, mval, mlen])
    (by intro m hm; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm; rcases hm with rfl | rfl | rfl <;> simp)
    (by decide +kernel)

#print axioms pass_halt_leaf
#print axioms pass_class_halt
#print axioms chain_class_halt

end BB6
