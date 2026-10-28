# End to end: what a halt from blank tape needs

`thm/EndToEnd.lean` puts the Lean results together into one statement about the machine
`1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE` started on blank tape. It does not settle the question. It says exactly
where a halt would have to come from: a clean tape of width at least 2³² that the clean-tape tree leaves open at
**every** depth. The classes it leaves open are exactly the exhaustive check's open classes: at 36 digits 1,660,024 of
measure 2.4 × 10⁻⁵, at 40 digits 9,188,898 of measure 8.4 × 10⁻⁶. With the clean tapes below 2⁴¹ in those classes run
one by one (`thm/EndToEndDirect.lean`, 26,508,327 runs), the clean tape a halt needs is at least 2⁴¹ wide. The same
statement from width 2²⁰ (`blank_halt_structure_kernel`) is checked by Lean's kernel alone, with no `native_decide`; the
tree it uses, over the widths ≥ 2²⁰, leaves the same classes open. With the loop entries (`thm/CleanEntryHalt.lean`,
below), the clean-tape tree also stops at the pass starts from which no member of the class can close through the loop,
and a halt needs a clean tape in its cut classes at every depth (at 36 digits 1,255,963 classes, measure 1.83 × 10⁻⁵,
over the widths ≥ 2⁴¹), or such a loop entry, from which the loop's chain ends without a close where the run leaves
three walls. The pass-start trees (`thm/PassHalt.lean`) follow the run on from there, and the two join
(`thm/PassEntryHalt.lean`, `blank_halt_pass`): a halt from blank tape needs a clean tape of width ≥ 2⁴¹ in a cut class
of the clean-tape tree with loop entries at every depth, or a pass start wider than 2⁴¹ in a cut class of its pass-start
tree at every depth. Some pass starts in those classes do halt (`pass_r6_halt`, `thm/PassHaltR6.lean`). But the run
reaches such a pass start only after a clean tape that the clean-tape tree without loop entries leaves open at every
depth, since that tree follows the run on through every entry (`blank_halt_open`). And its loop chain ends at none
with a right end below 178, where every known halt from a pass start closes (`thm/SmallEndHalt.lean`,
`blank_halt_small`, below): past a loop entry from
which no run of full passes ends at a right end below 178, the loop's chain ends at R ≥ 178, and at 36 digits every loop
entry is such an entry. So the question is whether the run from blank tape reaches one of the clean tapes of
`blank_halt_clean_direct`, and, if it passes a loop entry after it, one of the pass starts in the tree for every R ≥ 178
that it cuts at every depth; at every depth measured (up to 24 splits) that tree's cuts are all depth cuts, none at a
round decided as a halt. `blank_halt_open_small` (`thm/OpenSmallHalt.lean`) says both at once, and
`never_halts_of_open` turns it into the two questions left. Some of those pass starts do halt, at every width: past the
end of the loop's chain their run enters the loop again and closes (`sym_open_halt`, `thm/PassOpenHalt.lean`, below).
So the second question is whether the run from blank tape reaches one, not whether one halts. It reaches none of the
29 families found so far (eight from scans, and one at each scale j = 10 to 30 of `reentry_open_halt`): the loop's
chain from a loop entry of the clean-tape tree ends at a pass start with W ≤ 64R + 6 or 15W ≤ 64(W − b), which they are
only below width 2³⁵ (`blank_halt_not_family`, `thm/WideHalt.lean`, below, "The pass starts a halt needs are wide").
That pass start also has its middle wall at least 15/64 of the width from the end (`blank_halt_open_far`,
`thm/FarHalt.lean`), and with that shape none of the eight routes by which the halting classes with R from 178 to 198
close can start from it (untrusted, below, "The middle wall is far from the end"). Its right end is at least 769
(`blank_halt_open_big`, `thm/BigEndHalt.lean`, below, "The chain ends at a right end of at least 769"): no run of full
passes from a loop entry ends lower, nor one after a round-7 break past 2⁴¹. That puts every halting class with R below
769 out of its reach, whatever the class's route: all those of the census at R from 178 to 262, at 294 and at 486,
including those that close with no pass start after the first. Past 769 the census finds two lanes of halting classes
that recur at every R ≡ 486 (mod 512 or 1,024) and every scale, and whether the run reaches one is open.

## The statement

```lean
theorem blank_halt_clean (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∃ W k, prefixWidth ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTree d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)

theorem blank_halt_loop (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∀ (R : Nat) (ms : List Mark) (W k : Nat), PassStart448 ms W R →
      steps k ⟨blank, blank, .A⟩ = some (roundStart ms W) →
      ∃ ks ms₁ W₁ R₁, LoopChain ms W R ks ms₁ W₁ R₁ ∧
        ((InCloseClass ms₁ W₁ R₁ ∧ ∃ t, Reach ⟨[], 1, ms₁, W₁⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
          ∃ n ms' W', roundsZ 1000 n ms₁ W₁ = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n ms₁ W₁, 3 ≤ d) ∧
            LoopEnd W₁ R₁ (passL1 ms₁ W₁) n (meetsRounds 1000 n ms₁ W₁) ms' W' ∧
            ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t))

theorem blank_halt_sigma (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :   -- the σ bound
    ∀ (R : Nat) (ms : List Mark) (W k : Nat), PassStart448 ms W R → ¬ SigmaOK R (passL1 ms W) →
      steps k ⟨blank, blank, .A⟩ = some (roundStart ms W) →
      ∃ ks ms₁ W₁ R₁, LoopChain ms W R ks ms₁ W₁ R₁ ∧
        ((InCloseClass ms₁ W₁ R₁ ∧ (StepKind.half ∈ ks ∨ StepKind.break7 ∈ ks) ∧ ∃ t, …) ∨ …as above…)
-- SigmaOK R L := 256 ^ 2 * R ^ 3 ≤ 176 ^ 3 * L ^ 2

theorem blank_halt_wide (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :   -- no round-7 break
    ∀ (R : Nat) (ms : List Mark) (W k : Nat), PassStart448 ms W R → 2 ^ 24 ≤ W →
      steps k ⟨blank, blank, .A⟩ = some (roundStart ms W) →
      ∃ ks ms₁ W₁ R₁, LoopChain ms W R ks ms₁ W₁ R₁ ∧
        ((InCloseClass ms₁ W₁ R₁ ∧
            (∃ p, (ks = List.replicate p .full ∧ R = 16 ^ p * R₁ ∧ passL1 ms W = 64 ^ p * passL1 ms₁ W₁) ∨
              (ks = .half :: List.replicate p .full ∧ W % 4 = 2 ∧ R = 2 * 16 ^ p * R₁ ∧
                2 * 64 ^ p * passL1 ms₁ W₁ = passL1 ms W + 35 * (W : Int) - 147 * (R : Int) - 60)) ∧ ∃ t, …) ∨
          …as above…)

theorem blank_halt_exit (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∀ a b c E k, …loop state, gaps ≥ 390… →
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E) →
      ∃ n ms' W', roundsZ 1000 n … = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n …, 3 ≤ d) ∧
        ExitEvent n (meetsRounds 1000 n …) ms' W' ∧
        ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)

theorem blank_halt_structure (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) : … -- the three together

theorem never_halts_of_cut_classes
    (h : ∀ W, prefixWidth ≤ W → W % 2 = 0 → (∀ d, (cleanTree d).cutMem [(W : Int) / 2, 0] = true) →
      ∀ T, steps T (roundStart [⟨.M, W - 2⟩] W) ≠ none) :
    ∀ T, steps T ⟨blank, blank, .A⟩ ≠ none

theorem blank_halt_clean_direct (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :   -- thm/EndToEndDirect.lean
    ∃ W k, directWidth ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)

theorem blank_halt_clean_kernel (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :   -- no native_decide
    ∃ W k, kernelPrefixWidth ≤ W ∧ W % 2 = 0 ∧
      (∀ d, (cleanTreeG kernelPrefixWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)

theorem blank_halt_structure_kernel (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) : …
  -- blank_halt_clean_kernel, blank_halt_loop and blank_halt_exit together

theorem never_halts_of_cut_classes_kernel
    (h : ∀ W, kernelPrefixWidth ≤ W → W % 2 = 0 →
      (∀ d, (cleanTreeG kernelPrefixWidth d).cutMem [(W : Int) / 2, 0] = true) →
      ∀ T, steps T (roundStart [⟨.M, W - 2⟩] W) ≠ none) :
    ∀ T, steps T ⟨blank, blank, .A⟩ ≠ none

theorem blank_halt_clean_entry (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :   -- thm/CleanEntryHalt.lean
    (∃ W k, directWidth ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTreeGE directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
    ∃ ms W k, directWidth < W ∧ EntryNoClose ms W ∧ steps k ⟨blank, blank, .A⟩ = some (roundStart ms W) ∧
      steps (T - k) (roundStart ms W) = none ∧
      ∃ R ks ms₁ W₁ R₁, PassStart448 ms W R ∧ LoopChain ms W R ks ms₁ W₁ R₁ ∧
        ∃ n ms' W', roundsZ 1000 n ms₁ W₁ = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n ms₁ W₁, 3 ≤ d) ∧
          (LeftPhase0 n ms' ∨ ChainBreak (meetsRounds 1000 n ms₁ W₁)) ∧ NotWWW ms' ∧
          ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)

theorem blank_halt_clean_entry_kernel (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) : …
  -- the same from 2²⁰ (kernelPrefixWidth, the kernel's prefix), with no native_decide: the clean tape is cut at
  -- every depth by cleanTreeG kernelPrefixWidth d if W < 2²⁴, by cleanTreeGE (2 ^ 24) d if not

theorem blank_halt_pass (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :   -- thm/PassEntryHalt.lean
    (∃ W k, directWidth ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTreeGE directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
    ∃ R a b W k, directWidth < W ∧ PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R ∧
      (∀ d, PassCut d R a b W) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) ∧
      steps (T - k) (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)

theorem blank_halt_pass_kernel (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) : …
  -- the same from 2²⁰ with no native_decide: the clean tape is cut at every depth by cleanTreeG kernelPrefixWidth d
  -- if W < 2²⁴, by cleanTreeGE (2 ^ 24) d if not, and the pass start is at least 2²⁴ wide

theorem blank_halt_open (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :   -- thm/PassEntryHalt.lean
    ∃ W k, directWidth ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      (((∀ d, (cleanTreeGE directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
          ∃ u, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ u ∧ u.wf ∧ (EndClose u ∨ InteriorContact u)) ∨
        ∃ R a b W₁ t, W < W₁ ∧ PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁ R ∧
          (∀ d, PassCut d R a b W₁) ∧
          steps t (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) ∧
          steps (T - k - t) (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) = none ∧
          ∃ u, Reach ⟨[], 1, [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩], W₁⟩ u ∧ u.wf ∧
            (EndClose u ∨ InteriorContact u))

theorem blank_halt_open_kernel (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) : …
  -- the same from 2²⁰ with no native_decide: the clean tape is cut at every depth by cleanTreeG kernelPrefixWidth d,
  -- in the first case also by cleanTreeGE (2 ^ 24) d if W ≥ 2²⁴, and the pass start is at least 2²⁴ wide

theorem blank_halt_small (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :   -- thm/SmallEndHalt.lean
    (∃ W k, directWidth ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTreeGS directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧ …as in blank_halt_pass…) ∨
    ∃ R a b W k, directWidth < W ∧ 178 ≤ R ∧ PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R ∧
      (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W : Int) / 2, (R : Int) / 2] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) ∧ …as in blank_halt_pass…

theorem blank_halt_small_kernel (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) : …
  -- the same from 2²⁰ with no native_decide: the clean tape is cut at every depth by cleanTreeG kernelPrefixWidth d
  -- if W < 2³⁷, by cleanTreeGS (2 ^ 37) d if not, and the pass start is at least 2³⁷ wide, with R ≥ 178

theorem blank_halt_open_small (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :   -- thm/OpenSmallHalt.lean
    ∃ W k, directWidth ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      (((∀ d, (cleanTreeGS directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
          ∃ u, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ u ∧ u.wf ∧ (EndClose u ∨ InteriorContact u)) ∨
        ∃ R a b W₁ t, W < W₁ ∧ 178 ≤ R ∧ PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁ R ∧
          (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W₁ : Int) / 2, (R : Int) / 2] = true) ∧
          steps t (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) ∧
          …as in blank_halt_open…)

theorem blank_halt_open_small_kernel (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) : …
  -- the same from 2²⁰ with no native_decide: the clean tape is cut at every depth by cleanTreeG kernelPrefixWidth d,
  -- in the first case also by cleanTreeGS (2 ^ 37) d if W ≥ 2³⁷, and the pass start is at least 2³⁷ wide

theorem never_halts_of_open
    (hC : ∀ W, directWidth ≤ W → W % 2 = 0 → (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) →
      (∀ d, (cleanTreeGS directWidth d).cutMem [(W : Int) / 2, 0] = true) →
      ∀ T, steps T (roundStart [⟨.M, W - 2⟩] W) ≠ none)
    (hP : ∀ W R a b W₁ t, directWidth ≤ W → W % 2 = 0 →
      (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) → W < W₁ → 178 ≤ R →
      PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁ R →
      (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W₁ : Int) / 2, (R : Int) / 2] = true) →
      steps t (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) →
      ∀ T, steps T (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) ≠ none) :
    ∀ T, steps T ⟨blank, blank, .A⟩ ≠ none

theorem blank_halt_open_wide (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) : …   -- thm/WideHalt.lean
  -- blank_halt_open_small with cleanTreeGW for cleanTreeGS, and the pass start has the wide shape
  -- W₁ ≤ 64 * R + 6 ∨ 15 * W₁ ≤ 64 * (W₁ - b); blank_halt_open_wide_kernel is the same from 2²⁰, and
  -- never_halts_of_wide is never_halts_of_open with the shape among the pass start's hypotheses

theorem blank_halt_open_far (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) : …   -- thm/FarHalt.lean
  -- blank_halt_open_wide with cleanTreeGF for cleanTreeGW, and the pass start has 15 * W₁ ≤ 64 * (W₁ - b);
  -- blank_halt_open_far_kernel is the same from 2²⁰, and never_halts_of_far is never_halts_of_open with that

theorem blank_halt_open_big (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) : …   -- thm/BigEndHalt.lean
  -- blank_halt_open_far with cleanTreeGB for cleanTreeGF, and the pass start has 769 ≤ R as well;
  -- never_halts_of_big is never_halts_of_open with both

theorem blank_halt_not_family (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :   -- thm/WideHalt.lean
    ∃ W k, directWidth ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ((∀ d, (cleanTreeGW directWidth d).cutMem [(W : Int) / 2, 0] = true) ∨
        ∃ R a b W₁ t, W < W₁ ∧ 178 ≤ R ∧ PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁ R ∧
          …as in blank_halt_open_small… ∧
          ∀ F ∈ openHaltFams ++ reentryFams, ∀ s, ¬ (R = F.R0 ∧ b = F.b0 + 2 ^ F.k * s ∧ W₁ = F.W0 + 2 ^ F.k * s))
```

In words: if the machine halts from blank tape, then

1. on the way it reaches a **clean tape** (the gap at 1, then only the end marker M at W − 2) of even width
   W ≥ 2³² = 4,294,967,296 whose half W/2 lies in a **cut class** of the clean-tape tree **at every depth** d, and it
   halts from that clean tape;
2. the mark model, run on from that clean tape, reaches a **stuck configuration**: a close at the right end (the gap
   meets the end marker at distance 0, or touches a block at the end of the tape) or an interior contact;
3. from every **phase-0 pass start** it passes on the way (walls at a, b, E − R − 1, width E, a odd, b even, E even,
   every gap ≥ 448: `PassStart448`; left countdown L₁ = 147 b + 280 E − 392 (E − R − 1) − 578), the run follows
   **the loop's chain** (`LoopChain`): full passes, breaks of the end-meeting chain at round 7 and a half pass (only
   as the first step), each close-free and with its exact map on the width, the right end and the left countdown
   (below), each to a pass start whose gaps are again all ≥ 448, to the last of them (right end R₁); and the halt
   needs a stuck configuration after it: either right there, with R₁ in the closing set
   {2, 4, 8, 16, 24, 32, 48, 64, 176} and the left countdown in R₁'s class (`InCloseClass`; then
   **R³/L₁² ≤ 176³/256²** at the start of the chain's last run of full passes, `SigmaOK`: log₂W ≤ σ + 6.38, below),
   or after a further close-free stretch to where the run leaves the chain (`LoopEnd`: a round start that is not three
   walls after the run left phase 0 or the halving chain, or a landing with a gap below 448, which from a width
   ≥ 2¹³ needs a half pass from a middle wall within 896 of the end: below);
4. every **loop state** it passes on the way (walls at a, b, c, width E, a odd, b even, c odd, E even, every gap ≥ 390)
   is followed by the certified exit stretch, close-free to where it ends (`ExitEvent`: a clean tape, a break of the
   end-meeting chain, or a loop state again after a full pass), and the halt needs a stuck configuration after it.

`blank_halt_clean` is items 1 and 2, `blank_halt_loop` item 3, `blank_halt_exit` item 4, and `blank_halt_structure`
all four. `blank_halt_sigma` is item 3 at a pass start beyond the σ bound: there the run does not close through full
passes alone; its chain makes a half pass or a round-7 break first, or the halt needs a stuck configuration after the
chain's end. `blank_halt_wide` is item 3 at a pass start of width at least 2²⁴: a close through the loop from there
makes no round-7 break.

**The loop's chain** (October 27). The endgame trees' leaves that come back to three walls with the phase-0 parities
are of three kinds, and the end event (`Landing`, `StepMap` in `BB6/Ends.lean`) states each with its exact map on the
width E, the right end R and the left countdown L₁, as identities of forms checked by the kernel at every such leaf:

| step | rounds | R′ | L₁′ | W′ | first wall a′ (`StepWall`) |
|---|---|---|---|---|---|
| full pass | 8 | R/16 | L₁/64 | E + 24 | (b + 4c + 12E + 678)/64 |
| half pass, from E ≡ 2 (mod 4) | 2 | R/2 | (L₁ + 35E − 147R − 60)/2 | E + 6 | b/2 + 5 |
| break of the end-meeting chain at round 7 | 7 | (476E + 980R − L₁ + 15984)/4704 | (L₁ + 1120E + 1666R + 50328)/96 | E + 24 | (b + c + E + 135)/16 |

(b and c = E − R − 1 are the start's middle and last walls; the landing's middle wall follows from L₁′: it is
(b + 8c + 40E + 1258)/64, (b + c + 11)/2 and (3b + 6c + 10E + 452)/32.)

Of the trees' 1,877 leaves, 3 land after a full pass (one of them inside the closing class of R = 64), 44 after a half
pass (R ≡ 0 mod 4, R ≥ 8) and 12 after a round-7 break (R ≡ 12 mod 16); every other leaf ends at a round start that
is not three walls, or shows L₁ in a closing class. Every landing has W′ ≡ 0 (mod 4), so a
half pass is only ever the first step of a chain (`LoopChain.half_first`). At a round-7 landing
R′ = (4E + 4R − b + 110)/32 is set by the width rather than divided, and in the trees for R < 178 it is at least R; so
the chain is followed by induction on the halting time, not on R (`loop_chain_halt`): each step takes at least one
machine step, because the width grows and round starts of different widths are different configurations
(`passStart_ne`).

**Wide landings keep their gaps** (October 27). From these maps, every landing from a pass start of width E ≥ 2¹³
with every gap at least 448 is again a pass start with every gap at least 448 (`landing_wide`; a full pass needs
E ≥ 2,334 for a′ ≥ 448, a round-7 break E ≥ 6,138), except a half pass from a start whose middle wall b is within
896 of the end: its landing's last gap is (E − b)/2. Since a half pass is only ever the first step, the chain from a
pass start of width ≥ 2¹³ (with b + 896 ≤ E if E ≡ 2 mod 4) ends only where the run leaves phase 0 or the halving
chain at a round start that is not three walls (`loopEnd_wide`); `loop_halt_leaves` is `loop_halt_wide` with that
end. Below 2¹³ a pass can land with a gap below 448: from walls 449, 926, 1,375 and width 1,504 (R = 128) a full pass
lands at walls 393, 1,146, 1,519 (`lean --run RunWalls.lean 449 926 1504 128 9`).

**The σ bound** (October 27). At a pass start of width W with right end R and left countdown L₁, put s = log₂(W/R),
λ = log₂(|L₁|/W) and σ = 3s + 2λ (the notes' measure of how late a run enters the loop); then log₂W = σ + 3 log₂R −
2 log₂|L₁|. A full pass divides R by 16 and L₁ by 64 exactly, so R³/L₁² is the same at every pass start of a run of
full passes (`LoopChain.fulls`). At a close the right end is in the closing set and L₁′ in its class; with
L₁′ ≡ 3 (mod 7) each class bounds |L₁′| from below (4 for R₁ = 2 and 4, 24 for 8, 32 for 16 and 24, 192 for 32, 256
for 48, 64 and 176), and R₁³/L₁′² is at most 176³/256² (`sigma_close`, the R₁ = 176 class with |L₁′| = 256). So a
chain that ends in a closing class has R³/L₁² ≤ 176³/256² ≈ 83.19 at the start of its last run of full passes
(`LoopChain.sigma`), that is log₂W ≤ σ + 6.38 there: the bound of the notes (October 22), now a theorem. From a pass
start beyond the bound, a close through the loop needs a half pass or a round-7 break on the way (`loop_halt_sigma`,
`blank_halt_sigma`). The bound is attained: from the pass start with walls 601, 1,630, 9,323 and width 12,140
(R = 2,816, L₁ = −16,384, so R³/L₁² = 176³/256² exactly) the run makes a full pass to R = 176, L₁ = −256 (walls
2,895, 8,798, 11,987, width 12,164) and closes 13 rounds later (`lean --run RunWalls.lean 601 1630 12140 2816 24`).

**Wide pass starts make no round-7 break** (October 27). At a round-7 landing 32R′ = 4E + 4R − b + 110 and
96L₁′ = 147b + 1008E + 2058R + 50142, and the middle wall b is at most E − R − 449, so with S = 3E + 5R:
32R′ ≥ S and 0 < 96L₁′ ≤ 385S. R′³/L₁′² ≤ 176³/256² there needs 18432S ≤ 176³·385², that is S ≤ 43,841,661, so
E < 2²⁴ (`break7_sigma`; E ≤ 14,613,887). Widths grow along the chain, so from a pass start of width at least 2²⁴ a
close through the loop makes no round-7 break: the chain to it is p full passes (R = 16^p·R₁, L₁ = 64^p·L₁′), or a
half pass from W ≡ 2 (mod 4) and then p full passes (R = 2·16^p·R₁, 2·64^p·L₁′ = L₁ + 35W − 147R − 60)
(`LoopChain.close_wide`, `loop_halt_wide`, `blank_halt_wide`).

**From a pass start to the next checkpoint** (October 27). Where the loop's chain ends, `loop_chain_halt` only says
that a stuck configuration follows. The pass-start trees (`BB6/PassTree.lean`) follow the run on, round by round, to
the next *checkpoint*: a landing of the chain reached with every end meeting on the way at distance at least 3 (a step
of `LoopChain`), or a one-marker clean tape wider than the start. There is one tree for each R < 178 and one for every
R ≥ 178 with R a coordinate, each built by an explorer proved to build only trees that pass the check
(`PTree.explore_ok`), so `pass_next` (`thm/PassHalt.lean`) holds at every depth d with nothing evaluated: from every
pass start with gaps ≥ 448, L₁ is in R's closing class, or the start is in a cut leaf of its tree d splits deep
(`PassCut d R a b W`), or the run reaches a checkpoint without halting. `pass_halt_chain` chains the checkpoints by
induction on the halting time:

```lean
theorem pass_halt_chain (T : Nat) : ∀ (R a b W : Nat), PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R →
    2 ^ 13 ≤ W → (W % 4 = 2 → b + 896 ≤ W) →
    steps T (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = none →
    ∃ ks a₁ b₁ W₁ R₁,
      LoopChain [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R ks [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁ R₁ ∧
      (W₁ % 4 = 2 → b₁ + 896 ≤ W₁) ∧
      ((InCloseClass [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁ R₁ ∧ ∃ t, Reach ⟨[], 1, …, W₁⟩ t ∧ t.wf ∧ …) ∨
        (∀ d, PassCut d R₁ a₁ b₁ W₁) ∨
        ∃ k W', 0 < k ∧ k < T ∧ W < W' ∧ W' % 2 = 0 ∧
          steps k (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = some (roundStart [⟨.M, W' - 2⟩] W') ∧
          steps (T - k) (roundStart [⟨.M, W' - 2⟩] W') = none)
```

So a halt from a pass start of width ≥ 2¹³ follows the loop's chain to a last pass start, and there L₁ is in the
closing class and a stuck configuration follows, or the pass start is in a cut leaf at every depth, or the run goes on
to a wider clean tape, from which it halts in fewer steps; the clean-tape trees take over from there.

An end meeting at distance 2 is not a halt. In every closing class with R ≥ 4 the endgame trees' close is an end meeting
at distance 2, after which the round model goes on to a new round start; the pass-start trees run on through such
rounds, and only a landing reached that way is not a step of the chain (the tree runs past it, to a clean tape). A round
that the model decides otherwise (a halt, or a close at distance 0, which the model leaves uncovered) ends a path: at a
close leaf when L₁ is in R's closing class, at a cut otherwise. These are real halts. 1/8 of the pass starts with R = 6,
which is outside the closing set, leave phase 0 at round 2, meet the end at distance 2 in round 5 and at distance 0 in
round 7, at every width; from walls 743, 1,802, 3,319 and width 3,326 the machine halts after 11,362,209 steps, and all
49 such starts among 400 random ones of width below 8,400 halt when the machine is run (two simulators, from
`roundStart` as defined in `BB6/Marks.lean`). That is a theorem (`pass_r6_halt`, `thm/PassHaltR6.lean`, standard axioms
only): the kernel decides the six rounds on the whole class, to a round start whose only mark is a block three cells
before the width, and from such a round start, of width W′, the machine halts W′ + 65 steps later (`block_end_halt'`,
`BB6/BlockHalt.lean`: the head crosses the stripe to the block in W′ − 7 steps, meets it at distance 0 and stops 71
steps later). Of 40 random pass starts of width below 4,300 for each R, 14 halt with R = 4, 3 with R = 6, 7 with R = 8,
none with R = 10, 22 or 64. So the cut classes of the pass-start trees do not shrink to nothing; what `pass_halt_chain`
says is that a halt through a pass start needs one of them, or a closing class, or a clean tape after it.

Where the cone's edge leaves a round undecided and no residue split decides it (the first mark next to the gap at a
round start, where the members with the smallest value of the mark's position take another branch), the explorer
cleaves the class (`cleave`, at most `passCleaves` = 8 times on a path): the slice where that position takes its
extreme value goes on with one coordinate less, and the rest under a cone with that bound moved by one. The cut
leaves' measure (`PassStats.lean`; fractions of a start class, the slices having measure 0): at 16 splits 4.6% on
average over the trees for R < 178 (4.5% where the depth ran out, 0.1% at a decided halt, R = 6's 1/8), and 8.8% for
R ≥ 178; at 20 splits 2.0% (1.8% and 0.1%, and 4 × 10⁻⁶ at rounds that no cleave decides) and 3.8%, all of it where
the depth ran out; at 24 splits 1.6% for R ≥ 178 (the depth cuts fall about 0.8-fold per split). Before the cleaves it was
2.4% and 4.1% at 20 splits, with 0.7% of a class at undecided rounds, which more depth did not shrink. Landings take
12% of a class, clean tapes 84%, close leaves 1.6%.

**Every close at the right end is a halt** (`BB6/CloseHalt.lean`, `BB6/HaltTree.lean`, `thm/PassHaltClasses.lean`).
Every round that the model leaves uncovered in the samples ends at one configuration: the gap meets the end marker at
distance 0, a marker touches the gap from the left, and nothing lies past the end marker (`EndClose0`). From there the
machine halts 54 steps later, whatever lies further left (`end_close_local`, by `rfl`). Every event of the model is a
run of the machine (`Step.run`), so a close that the model reaches from a well-formed start is a halt
(`reach_close_halt`); with `halt_needs_end_close` the machine halts exactly when the model reaches one, wherever no
interior contact is reachable and every close at the right end is of this kind (`halt_iff_end_close`; both conditions
measured, not proved). The close run (`closeRun`, and `symCloseRun` on a class) follows the model across rounds to that
close, so it proves halts: of a concrete start, and of every member of a class (`symCloseRun_halt`). A halting tree
(`HTree.ofPTree`) has a pass-start tree's splits and a `halt` leaf wherever the close run closes a close or cut leaf's
class, and every pass start in a halting leaf halts, at every depth (`pass_halt_leaf`, nothing evaluated). At 12 to 20
splits the halting leaves are eight classes, by residues of the middle wall b and the width W (`HaltClass`): every pass
start with R = 2; with R = 4, those with W ≡ 0 (mod 4) and b ≡ 6 (mod 8) or W ≡ 2 (mod 4) and b ≡ 0 (mod 4) (3/8);
with R = 6, the eighth of `pass_r6_halt`; and with W ≡ 0 (mod 4), those with R = 8 and b ≡ 30 (mod 32), R = 16 and
b ≡ 30 (mod 64), R = 32 and b ≡ 30 + 16W (mod 128), and R = 48 and b ≡ 158 + 48W (mod 256) (1/32, 1/64, 1/128 and
1/256). No other R < 178 has one, though 24, 64 and 176 are in the closing set. Apart from R = 6's, they are exactly
the close leaves: every close leaf of the pass-start trees halts. `pass_class_halt` proves that each class halts (the
close run on each class, evaluated by the kernel, about two seconds for all eight), and `chain_class_halt` that a pass
start whose loop chain reaches one halts. In 600,000 random pass starts with R < 178 (widths 2¹² to 2³⁰), the model's
run ends at a one-marker clean tape (98.1%) or at the close (1.9%) and nowhere else, and every run that ends at the
close passes through a pass start in one of the classes. With R from 178 to 4,176 one run in 400,000 closes: from
walls at 786,501, 1,023,966 and 1,073,891 and width 1,074,148 (R = 256), it lands at R = 32 and then at R = 16, in a
class (`pass_halt_example_r256`). A halt from blank tape cannot end its loop chain in a class: `blank_halt_small` puts
the chain's last pass start at R ≥ 178, cut at every depth. Past it the run could still reach a class by entering the
loop again, through an end meeting off the chain whose own halving chain runs to 0: in samples run to the next landing
or clean tape, three of twelve million starts with R from 50 to 176 did (at width 2¹², through an end meeting at 254;
`pass_halt_example_reentry`), and none of ten million with R ≥ 178 (`../notes/LAB_NOTES.md`). With R ≥ 178 it happens
too, more rarely (below).

**Pass starts with R ≥ 178 that halt, open at every depth** (`thm/PassOpenHalt.lean`). In 50 million random pass
starts with R from 178 to 376 at widths 2¹¹ to 1.5 × 2¹¹, nine runs close before the next landing or clean tape, and 14
of 50 million at 2¹² (untrusted). The first found has walls at 1,523, 2,010 and 2,477 and width 2,656 (R = 178). Its run
leaves the loop in round 2, meets the end at 254 in round 5, off the chain, and closes in round 19 after the halving
chain 254, 126, …, 2, 0, through a pass start in the R = 16 class; it reaches no landing and no clean tape on the way.
The route depends on the right end and the two walls next to it, and on the middle wall only modulo 2¹⁴: every pass
start with walls at a, b and b + 467 and width b + 646, a odd, a ≥ 448, b − a ≥ 448 and b ≡ 2,010 (mod 2¹⁴), halts
and lies in a cut leaf of `passTreeSym` at every depth (`family_open_halt`). The kernel runs the model on the family,
on symbolic positions: 18 round starts none of which could be a checkpoint of `pass_next` (`symOpenRun`, then
`sym_open_of_run`), and the close run (`symCloseRun_halt`). So there are such pass starts at every width
(`sym_open_halt`) and above 2⁴¹ (`sym_open_halt_wide`): the second question of `never_halts_of_open` is not answered by
the pass start alone, only by whether the run from blank tape reaches one. The family is thin: at a given width only
its first wall is free. It is not alone. An untrusted scan of every pass start with R ≥ 178 and width from 2,048 to
3,072 (75 million placements of the second and third walls, three first walls for each) finds eleven placements whose
run closes, each for every first wall. Seven of them, this one among them, repeat with the other walls and the width
moved right by any multiple of 2¹³ to 2¹⁵, and the kernel checks each as a family (`open_halt_families`,
`Fam.open_halt`); the close run fails on such classes for the other four. Every route meets the end at R − 2, then
off the chain at 254, 510, 766 or 1,022 (2⁸ − 2, 2⁹ − 2, 3 · 2⁸ − 2, 2¹⁰ − 2), and that meeting's halving chain runs to
the close through three-wall round starts with R from 128 down to 2. The landings of the loop's chain do not avoid
them. A full pass from a pass start with every gap at least 448 lands on the plane 2(b − a) = W − 2R − 6
(`landing_plane`) with 16W − 64R + 1,188 ≤ 64a ≤ 17W − 80R − 183 (a, b, W and R the landing's). Of the 18.4 million
such points with R ≥ 178 and width up to 16,384, two close, at widths 13,400 and 16,292, and both are real full-pass
landings. The first lies in an eighth family, and `full_pass_open_halt` proves its chain: the pass start with walls at
449, 1,182 and 10,399 and width 13,376 (R = 2,976) makes a full pass onto walls at 3,187, 9,698 and 13,213 and width
13,400 (R = 186), which `passTreeSym` leaves open at every depth and from which the machine halts. Its route repeats
at every scale: the run meets the end at R − 2, then off the chain at (W − b + 2R + 14)/4, which W − b = 2^(j+2) − 2R − 22
puts at 2^j − 2, whose halving chain runs to the close, and for each j from 10 to 30 the kernel checks a family with
R = 178 there (`reentry_open_halt`, `reentryFams_shape`; the meetings are 176, 2^j − 2, 2^(j−1) − 2, …, 2, 0). For
each such j and each R ≡ 2 (mod 4) tried, a symbolic search of the model's rounds finds exactly one class of b that
closes, modulo about 2^(1.5j + 2): about 1.5 binary digits per halving (untrusted, `HaltClasses.lean`). With
R ≡ 6 (mod 8) the run has three walls in round 7, the half pass of a three-wall start in round 5, with right end
(W − b + 2R + 22)/16. That start is no landing of the loop's chain: a break of the chain at round 7 would need
4,704 R′ = 476 W + 980 R − L₁ + 15,984, and the difference is −294 (W − b) − 441 b − 9,702 < 0. `symOpenRun2` passes
such a round start (`notLandingCheck`: an identity of `StepMap` decidedly false on the class; `sym_open_of_run2`),
and with it the kernel checks the class with R = 182 for each j from 10 to 30 (`reentry6_open_halt`,
`reentryFams6_shape`) and a full pass from walls 449, 4,318 and 25,827, width 29,380 (R = 3,552), onto walls 7,201,
21,678 and 29,181, width 29,404 (R = 222), open at every depth, from which the machine halts (`full_pass_open_halt6`).
Above R = 483 there are halting lanes too: with Q = W − b + 2R + 22 = 2^(12+s) − 636 the run meets the end at R − 2,
then off the chain at Q/4 − 3 = 2^(10+s) − 162, and follows the chain from there to 0 (2^(6+s) − 12, then
2^(5+s) − 2, ..., 2, 0); its first three-wall round start after the first is in round 17,
with right end (Q + 636)/1,024, or on a second lane in round 13, with right end (Q + 636)/256, and that start's half
pass begins full passes to the close. An untrusted search finds one class of b on each lane at every scale and every
R ≡ 486 (mod 512), resp. (mod 1,024), tried up to 4,582, and the kernel checks the 38 at R = 486 for s = 0 to 18
(`lane486_open_halt`, `lane486_shape`). And four families at R = 230 halt with no three-wall round start after the
first (`no_pass_open_halt`, `symNoWWWRun`): no pass start lies between them and the halt. Three of the eleven
placements of the scan are landings of a half pass, the first step of a chain from a loop entry. Two in 18.4 million
is about the rate of random pass starts at those widths, and the pass-start tree run on the full-pass landings alone
leaves as much of its class open as `passTreeSym` does (8.6% at 16 splits, against 8.8%; untrusted). Random starts at
large widths almost never close
this way (none of 25 million each at 2²⁰, 2³⁰ and 2⁴¹), since the end meetings off the chain lie at distances of the
order of the width: runs with one below 2¹⁰ are 28% at width 2¹², 4% at 2¹⁶, 0.4% at 2²⁰, 0.03% at 2²⁴ and 3 in
400,000 at 2³⁰, about 0.55-fold per doubling of the width (`../notes/LAB_NOTES.md`).

**Why the stretches name their ends** (October 27). The first versions of items 3 and 4 said only "the model covers n
rounds from the start, with no close, and the halt needs a stuck configuration after them". With n = 0 that is just
the round theorem: it holds for every start, with no tree. The trees' leaves now end at events stated in
`BB6/Ends.lean`, none of which holds after zero rounds, so the stretches are real: from a pass start the run is
followed until it leaves phase 0 or breaks the end-meeting chain at a round start that is not three walls, or lands
on three walls again by one of the loop's three steps, and through every such landing whose gaps stay ≥ 448; from a
loop state, until a clean tape, a chain break, or a loop state again.

`never_halts_of_cut_classes` is item 1 read backwards: the open question is now only about the clean tapes of width
at least 2³² that the tree leaves open at every depth. Since `∀ d` includes d = 36 and d = 40, such a clean tape lies
in the cut classes whose measure `thm/CleanMass.lean` and `thm/CleanMass40.lean` evaluate.

`blank_halt_clean_direct` and `never_halts_of_cut_classes_direct` (`thm/EndToEndDirect.lean`) are items 1 and 2 with
2⁴¹ for 2³²: every clean tape of width in [2³², 2⁴¹) reaches a wider one (`clean_step_direct`, below), so the clean
tape a halt needs is at least 2⁴¹ wide, and it lies in the cut classes at every depth of `cleanTreeG 2⁴¹ d`, the same
exploration with the cone W ≥ 2⁴¹. They trust one more evaluation (`clean_direct_ok`).

`blank_halt_clean_kernel`, `blank_halt_structure_kernel` and `never_halts_of_cut_classes_kernel` are the same with
2²⁰ = 1,048,576 for 2³², and they trust no evaluation by compiled code: `#print axioms` lists `propext`,
`Classical.choice` and `Quot.sound` alone. The run from blank tape to the clean tape of width 2²⁰ is checked by Lean's
kernel (`blank_prefix_kernel`, below), and from there on the clean-tape tree over the widths ≥ 2²⁰
(`cleanTreeG 2²⁰ d`, from the same proved explorer) takes over: `blank_halt_clean_from` with A = B = 2²⁰, so nothing
is run in between. The lower cone costs nothing in the cut classes: with the cone's edge handled by drops (below), the
tree over the widths ≥ 2²⁰ leaves the same 1,660,024 classes open at 36 digits as the trees over the widths ≥ 2³² and
≥ 2⁴¹ (`thm/CleanKernelMass.lean`).

`blank_halt_clean_entry` (`thm/CleanEntryHalt.lean`) is items 1 and 2 above 2⁴¹ with the loop entries: the clean-tape
tree with loop entries (`cleanTreeGE`) stops a path at the first pass start from which no member of its class can close
through the loop, and a halt needs either a clean tape of width ≥ 2⁴¹ in its cut classes at every depth, or such a
loop entry, wider than 2⁴¹, from which the loop's chain ends without a close where the run leaves three walls (below,
"The clean tapes' loop entries"). `blank_halt_clean_entry_kernel` is the same from 2²⁰, with no `native_decide`.

`blank_halt_pass` (`thm/PassEntryHalt.lean`) follows the run on from such an entry with the pass-start trees (below,
"Past the loop's end, from blank tape"): a halt needs a clean tape of width ≥ 2⁴¹ in a cut class of
`cleanTreeGE 2⁴¹ d` at every depth, or a pass start wider than 2⁴¹ with every gap at least 448 that lies in a cut leaf
of its pass-start tree at every depth (`PassCut`); the machine halts from there, and the mark model reaches a stuck
configuration from there. `blank_halt_pass_kernel` is the same from 2²⁰, with no `native_decide`.

`blank_halt_open` (`thm/PassEntryHalt.lean`) puts `blank_halt_clean_direct` and `blank_halt_pass` together (below,
"The open clean tapes come first"): a halt needs a clean tape of width ≥ 2⁴¹ in a cut class of `cleanTreeG 2⁴¹ d` at
every depth, from which the machine halts; and either `cleanTreeGE 2⁴¹ d` leaves that clean tape open at every depth
too, and the mark model reaches a stuck configuration from it, or the run from it reaches a pass start that lies in a
cut leaf of its pass-start tree at every depth, halts from there, and the mark model reaches a stuck configuration from
there. `blank_halt_open_kernel` is the same from 2²⁰, with no `native_decide`.

`blank_halt_small` (`thm/SmallEndHalt.lean`) is `blank_halt_pass` with the clean-tape tree whose loop entries also pass
the small-end check (`cleanTreeGS`, below, "No small right end past the loop"): the pass start a halt needs has right
end R ≥ 178, so it lies in a cut leaf of the tree for every R ≥ 178 (`passTreeSym`) at every depth.
`blank_halt_small_kernel` is the same from 2²⁰, with no `native_decide` (the plain tree below 2³⁷, `cleanTreeGS 2³⁷ d`
above).

`blank_halt_open_small` (`thm/OpenSmallHalt.lean`) is `blank_halt_open` with `cleanTreeGS` as the tree with loop
entries and `entry_small_halt` at them: a halt needs a clean tape of width ≥ 2⁴¹ that `cleanTreeG 2⁴¹ d` leaves open at
every depth, from which the machine halts; and either `cleanTreeGS 2⁴¹ d` leaves it open too, and the mark model
reaches a stuck configuration from it, or the run from it passes a loop entry and reaches a pass start with R ≥ 178
that `passTreeSym d` leaves open at every depth, halts from there, and the mark model reaches a stuck configuration
from there. `blank_halt_open_small_kernel` is the same from 2²⁰, with no `native_decide`. `never_halts_of_open` turns
it around: the machine never halts from blank tape if it halts from no clean tape that both trees leave open at every
depth, and from no pass start with R ≥ 178 that `passTreeSym d` leaves open at every depth and that the run reaches
from a clean tape that `cleanTreeG 2⁴¹ d` leaves open at every depth.

`blank_halt_open_wide` (`thm/WideHalt.lean`) is `blank_halt_open_small` with the clean-tape tree whose loop entries
also have W ≤ 32R (`cleanTreeGW`) and `entry_wide_halt` at them (below, "The pass starts a halt needs are wide"): the
pass start a halt needs also has W₁ ≤ 64R + 6 or 15W₁ ≤ 64(W₁ − b). `blank_halt_open_wide_kernel` is the same from
2²⁰, with no `native_decide`, and `never_halts_of_wide` is `never_halts_of_open` with only the pass starts of that
shape to rule out. `blank_halt_not_family` is `blank_halt_open_wide` with the shape turned into the families: the pass
start it names is a member of none of the eight families of `open_halt_families` nor of the 21 of
`reentry_open_halt`. `blank_halt_open_far` (`thm/FarHalt.lean`) is `blank_halt_open_wide` with the tree whose loop
entries have their middle wall far from the end (`cleanTreeGF`): the pass start a halt needs has 15W₁ ≤ 64(W₁ − b)
(below, "The middle wall is far from the end"); `blank_halt_open_far_kernel` and `never_halts_of_far` are as for the
wide shape. `blank_halt_open_big` (`thm/BigEndHalt.lean`) is `blank_halt_open_far` with the tree whose far loop
entries also end at no right end below 769 (`cleanTreeGB`): the pass start a halt needs has R ≥ 769 as well (below,
"The chain ends at a right end of at least 769"), and `never_halts_of_big` leaves only those pass starts to rule out;
there is no kernel-only version.

## The pieces

| file | result | how |
|---|---|---|
| `thm/Prefix.lean` | `blank_prefix`: from blank tape the machine reaches the clean tape of width exactly 2³², without halting | the mark model from the first round start, 1,204,297,272 rounds, evaluated by `native_decide`, then `blank_rounds` |
| `thm/PrefixKernel.lean` (generated by `thm/gen_prefix.py` from the checkpoints of `PrefixGen.lean`) | `blank_prefix_kernel`: from blank tape the machine reaches the clean tape of width exactly 2²⁰, without halting | 294,033 rounds in 59 stretches of 5,000, each checked by the kernel (`decide +kernel`, `thm/PrefixPieces*.lean`), chained by `roundsZ_chain` |
| `BB6/CleanTree.lean` | `RTree.okW` / `RTree.soundW`: a route tree whose `clean` leaves are one-marker clean tapes **wider** than the start, with `drop` nodes (`dropOK`: the smallest member of a class run directly, `toWider`, and the rest of the class continued); `roundStart_one_ne`: clean tapes of different widths are different configurations | proved, standard axioms |
| `BB6/RouteExplore.lean` | `RTree.exploreW`: builds the clean-tape tree to any depth, dropping the smallest member of a class where the cone's edge leaves a round undecided; `exploreW_okW`: every tree it builds passes `RTree.okW`; `exploreMassW`: its cut measure and leaf counts without the tree | proved, standard axioms |
| `thm/CleanTheorem.lean` | `clean_tree_step_G`: for every Γ ≥ 6 and every depth d, from every clean tape of even width W ≥ Γ, the machine reaches a wider clean tape without halting, unless W/2 is in a cut class of `cleanTreeG Γ d`; `clean_tree_step` is Γ = 2³² (`cleanTree d`) | `RTree.soundW` and `exploreW_okW`; nothing evaluated |
| `thm/EndgameTheorem.lean`, `thm/LoopTheorem.lean` | `endgame_stretch`: from a phase-0 pass start with gaps ≥ 448, a close needs R in the closing set and L₁ in R's class, and otherwise the run is close-free to an end event: a round start that is not three walls after it leaves phase 0 or breaks the chain, or a landing (a full pass, a half pass or a round-7 break, with its exact map on E, R and L₁); `loop_step`, `LoopChain`: the chain of these steps through pass starts with gaps ≥ 448; `LoopChain.sigma`: a chain that ends in a closing class has R³/L₁² ≤ 176³/256² at the start of its last run of full passes; `break7_sigma`, `LoopChain.close_wide`: from a width ≥ 2²⁴ it makes no round-7 break | the endgame trees checked by the kernel (`Tree.okEnd`, `decide +kernel`); the closing classes with L₁ ≡ 3 mod 7 |
| `thm/ExitTheorem.lean` | `exit_stretch`: from a loop state with gaps ≥ 390, the run is close-free to an exit event (`ExitEvent`) | the exit tree checked by the kernel (`Tree.okEnd`, `decide +kernel`) |
| `thm/LoopHalt.lean`, `thm/ExitHalt.lean` | `loop_chain_halt`: a halt from a phase-0 pass start with gaps ≥ 448 needs a stuck configuration after the loop's chain from it; `exit_halt_needs_contact`: one from a loop state, after the certified exit stretch; `loop_halt_sigma`: beyond the σ bound, a close needs a half pass or a round-7 break on the way; `loop_halt_wide`: from a width ≥ 2²⁴, no round-7 break; `loop_halt_leaves`: and the chain ends where the run leaves three walls | `loop_step` and `halt_after_rounds`, by induction on the halting time (each step takes at least one machine step: `passStart_ne`); `exit_stretch` |
| `BB6/PassTree.lean`, `thm/PassHalt.lean` | `PTree.sound`: a pass-start tree's check gives, at every point of its class, a cut leaf, the left countdown in the closing class, or a halt-free run to a close-free landing of the chain or a wider clean tape; `PTree.explore_ok`: every tree the explorer builds passes the check (it cleaves a class where the cone's edge leaves a round undecided); `pass_next`: from every pass start with gaps ≥ 448, at every depth; `pass_halt_chain`: a halt from a pass start of width ≥ 2¹³ follows the chain to a last pass start in a closing class, or cut at every depth, or goes on to a wider clean tape | the proved explorer, nothing evaluated; induction on the halting time through `landing_wide` and `halt_after_rounds` |
| `BB6/BlockHalt.lean`, `thm/PassHaltR6.lean` | `block_end_halt'`: from a round start whose only mark is a block three cells before an odd width W ≥ 9, the machine halts within W + 65 steps; `pass_r6_halt`: every phase-0 pass start with R = 6, b ≡ 2 (mod 8), W ≡ 2 (mod 4) and gaps ≥ 448 halts | `pass` and 72 steps by `rfl`; the six rounds on the class by `symRoundsZ`, `decide +kernel` |
| `BB6/CloseHalt.lean`, `BB6/HaltTree.lean`, `thm/PassHaltClasses.lean` | `reach_close_halt`: a close at the right end with the end marker at distance 0 (`EndClose0`) that the model reaches from a well-formed start is a halt; `halt_iff_end_close`: where no interior contact is reachable and every such close is of this kind, the machine halts exactly when the model reaches one; `closeRun_sound`, `symCloseRun_halt`: the close run proves halts, of a start and of a class; `pass_halt_leaf`: every pass start in a halting leaf of a pass-start tree halts, at every depth; `pass_class_halt`: every pass start in a halting class (`HaltClass`: R = 2, 3/8 of R = 4, 1/8 of R = 6, 1/32, 1/64, 1/128 and 1/256 of R = 8, 16, 32 and 48) halts; `chain_class_halt`: so does every pass start whose loop chain reaches one | the model's events as runs of the machine (`gapEvent_ok`, `pktBack_run`, `pktLand_run`) and the close's 54 steps by `rfl`; `HTree.sound` and `HTree.ofPTree_ok`, nothing evaluated; the close run on each class by `decide +kernel` |
| `thm/PassOpenHalt.lean` | `family_open_halt`: every pass start with walls at a, b and b + 467 and width b + 646 (R = 178), a odd, a ≥ 448, b − a ≥ 448 and b ≡ 2,010 (mod 2¹⁴), lies in a cut leaf of `passTreeSym` at every depth and halts; `sym_open_halt`, `sym_open_halt_wide`: such pass starts at every width, and above 2⁴¹; `open_halt_families`: the same for eight families (first wall free, the other walls and the width moved by multiples of 2¹³ to 2¹⁷); `full_pass_open_halt`: a full pass of the loop's chain (`LoopChain`, R = 2,976 to R = 186) lands on a member of the eighth; `reentry_open_halt`: the eighth's route at each scale j from 10 to 30, a family with R = 178 and W − b = 2^(j+2) − 378 (`reentryFams_shape`); `reentry6_open_halt`: the same with R = 182 (`reentryFams6_shape`); `full_pass_open_halt6`: a full pass (R = 3,552 to R = 222) onto a member of the class at width 29,404; `sym_open_of_run`: a pass start with R ≥ 178 whose model run leaves a round uncovered before any possible checkpoint is cut at every depth, and `sym_open_of_run2` the same before any checkpoint; `no_pass_open_halt`: four families with R = 230 that halt with no three-wall round start after round 0; `lane486_open_halt`: two families with R = 486 at each scale W − b = 2^(12+s) − 1,630, s = 0 to 18 | `pass_next` with `no_checkpoint`; the model's rounds on each family (`symOpenRun`, or `symOpenRun2` with `notLandingCheck` where a three-wall round start is decidedly not a landing, `symRoundsZ_sound`) and the close run (`symCloseRun_halt`) by `decide +kernel`, as are the full pass's eight rounds (`rounds_run`) and the round starts' types (`symNoWWWRun`) |
| `thm/LaneHalt.lean` | `lane769_open_halt`: 36 families of pass starts with R ≥ 769 (first wall free, the other walls and the width moved by multiples of 2^k), each lying in a cut leaf of `passTreeSym` at every depth and halting: one on each lane of the census at R = 770 to 1,004 and δ at R = 998 at each scale W − b = 2^j − 2,654, j = 13 to 30 (`lanes769`, `delta998`); `lanes769_shape`: each family's R and Q = W − b + 2R + 22; `lane769_far`: a member with 15W ≤ 64(W − b), width 16,192; `route769_open_halt`: 21 more on the routes that census does not find, ζ at R = 998 at eleven scales from 2^14 to 2^22 and ε′, the four Q + 316 routes at R ≡ 230 and ε from the census at R = 5,002 to 5,862 (`zeta998`, `routes5000`, `routes_shape`) | `Fam.open_halt`; the close run and the model's rounds on each family by `decide +kernel` |
| `thm/EndToEnd.lean` | `clean_chain`, `blank_halt_clean_from`, `blank_halt_clean`, `blank_halt_clean_kernel`, `blank_halt_loop`, `blank_halt_sigma`, `blank_halt_wide`, `blank_halt_exit`, `blank_halt_structure`, `blank_halt_structure_kernel`, `never_halts_of_cut_classes`, `never_halts_of_cut_classes_kernel` | strong induction on the halting time: at each clean tape, either it is cut at every depth, or some depth decides it and the run goes on to a wider clean tape, which takes at least one machine step |
| `thm/RouteTheorem.lean`, `thm/RouteEntryTheorem.lean`, `thm/RouteEntryHalt.lean` (`ROUTE_TREE.md`) | `route_tree_clean`, `route_tree_entry`: from every two-marker state with both gaps ≥ Γ, a halt-free run to a clean tape, or (`routeTreeE`) to a loop entry from which no point of its class closes through the loop, unless the start is in a cut class; `entry_halt`, `route_halt`, `blank_halt_route`: a halt from such an entry needs the loop's chain to end without a close where the run leaves three walls, and a stuck configuration after it, and so does a halt from blank tape at each such two-marker state it passes, unless the state is cut at every depth | `RTree.sound`, `RTree.soundE` with the proved explorers (`explore_ok`, `exploreE_okE`); `entryOK_sound`, `EntryNoClose.no_close` (`LoopChain.close_wide`) and `loop_halt_leaves`; nothing evaluated |
| `thm/CleanMass.lean`, `thm/CleanMass40.lean` | `clean_tree_cut_mass`, `clean_tree_cut_mass40`: the leaf counts and cut measure of `cleanTree 36` and `cleanTree 40` | `exploreMassW` evaluated by `native_decide`; used by no theorem about the machine |
| `thm/CleanKernelMass.lean` | `clean_kernel_cut_mass`: the leaf counts and cut measure of `cleanTreeG 2²⁰ 36` | `exploreMassW`, `native_decide`; used by no theorem about the machine |
| `BB6/CleanRange.lean` | `directOK_sound`: a run of the mark model from a clean tape to a wider one, as a statement about the machine; `RTree.cuts1_sound`: the cut classes of a one-variable tree as residues of W/2; `rangeOK_sound`: every clean tape of width in [lo, hi) that the tree leaves open runs directly to a wider one | proved, standard axioms |
| `thm/CleanDirect.lean` | `clean_step_direct`: every clean tape of even width in [2³², 2⁴¹) reaches a wider clean tape, with no exception | `rangeOK` on `cleanTree 36` evaluated by `native_decide` (26,508,327 members of the cut classes, each run to a wider clean tape), and `clean_tree_step` for the rest |
| `thm/EndToEndDirect.lean` | `blank_halt_clean_direct`, `never_halts_of_cut_classes_direct` | `blank_halt_clean_from` (`thm/EndToEnd.lean`: the chain from a clean tape the run reaches, for any bounds A ≤ B with every clean tape of width in [A, B) reaching a wider one, with the tree `cleanTreeG B d` above B) with the prefix to 2³², A = 2³² and B = 2⁴¹ |
| `thm/CleanDirectMass.lean`, `thm/CleanDirectMass40.lean` | `clean_direct_cut_mass`, `clean_direct_cut_mass40`: the leaf counts and cut measure of `cleanTreeG 2⁴¹ 36` and `cleanTreeG 2⁴¹ 40` | `exploreMassW`, `native_decide`; used by no theorem about the machine |
| `BB6/CleanEntryTree.lean` | `RTree.okWE` / `RTree.soundWE`: a clean-tape tree with `entry` leaves checked by a given test; `RTree.exploreWE`: the explorer `RTree.exploreW` that also stops a path at the first round start passing the test, with `exploreWE_okWE`; `cleanEntryOK`: `entryOK` (`BB6/RouteEntry.lean`) and the entry decided to be wider than the start | proved, standard axioms |
| `thm/CleanEntryTheorem.lean` | `clean_tree_entry_step`: for every Γ ≥ 6 and every depth d, from every clean tape of even width W ≥ Γ, the machine reaches a wider clean tape or a wider loop entry that cannot close (`EntryNoClose`) without halting, unless W/2 is in a cut class of `cleanTreeGE Γ d` | `RTree.soundWE` and `exploreWE_okWE`; nothing evaluated |
| `thm/CleanEntryHalt.lean` | `clean_entry_chain`: the chain over clean tapes for bounds A and B as in `blank_halt_clean_from`, with, as hypotheses, the step at each width ≥ B (to a cut class, a wider clean tape or a wider loop entry that cannot close) and what a halt from a loop entry needs (a property `Q` of the entry, or a wider clean tape the run reaches from it); `blank_halt_clean_entry_from`, `blank_halt_clean_entry` (prefix to 2³², direct runs to 2⁴¹, the tree with entries above), `blank_halt_clean_entry_kernel` (from 2²⁰, the plain tree below 2²⁴ and the tree with entries above; no `native_decide`) | strong induction on the halting time, as `clean_chain`; at an entry, `entry_halt` |
| `thm/PassEntryHalt.lean` | `LoopChain.reach`: the loop's chain is a run of the machine; `entry_pass_halt`: a halt from a loop entry that cannot close needs the loop's chain to a last pass start in a cut leaf of its pass-start tree at every depth, or a wider clean tape that the run reaches and halts from; `blank_halt_pass_from`, `blank_halt_pass`, `blank_halt_pass_kernel`: from blank tape, a clean tape cut at every depth or such a pass start; `clean_entry_chain_open`, `blank_halt_open_of` (for any test of the loop entries), `blank_halt_open_from`, `blank_halt_open`, `blank_halt_open_kernel`: the clean tape is cut at every depth by the tree without loop entries, and then by the tree with them too, or such a pass start follows; `LoopChain.last_halt`; `landing_plane`: every landing has 2(b − a) = W − 2R − 6 | `pass_halt_chain` with `EntryNoClose.no_close`, as `clean_entry_chain`'s hypothesis on the entries; for `blank_halt_open`, the step of `cleanTreeG` where it does not cut at every depth, else that of `cleanTreeGE`; nothing evaluated |
| `BB6/SmallEnd.lean` | `NoSmallAt`: no run of full passes ends at a right end below 178; `smallOK_sound`: on a class of one coordinate, at every point of the cone; `smallEntryOK_sound`: at a loop entry, also after a half pass, with the width ≥ 2³⁷ (`EntryNoSmall`); `cleanSmallOK`: `cleanEntryOK` and that | proved, standard axioms |
| `thm/CleanSmallTheorem.lean`, `thm/CleanSmallMass.lean` | `clean_tree_small_step`: as `clean_tree_entry_step`, with `cleanTreeGS Γ d` and entries that also satisfy `EntryNoSmall`; `clean_tree_small_cut_mass`: at 36 digits over the widths ≥ 2⁴¹ the same counts as `cleanTreeGE` | the proved explorer, nothing evaluated; the counts by `exploreMassWE` and `native_decide`, used by no theorem about the machine |
| `thm/SmallEndHalt.lean` | `noSmall_sigma`, `break7_noSmall`, `LoopChain.small_end`: the chain from a pass start of width ≥ 2³⁷ with `NoSmallAt` (and after a half pass) ends at R ≥ 178; `entry_small_halt`; `blank_halt_small`, `blank_halt_small_kernel`: from blank tape, a clean tape cut at every depth or a pass start with R ≥ 178 cut at every depth of `passTreeSym` | R³/L₁² through the chain's steps; `entry_pass_halt` and `clean_entry_chain_of`; nothing evaluated |
| `thm/OpenSmallHalt.lean` | `blank_halt_open_small`, `blank_halt_open_small_kernel`: the clean tape is cut at every depth by `cleanTreeG`, and then by `cleanTreeGS` too, or a pass start with R ≥ 178 cut at every depth of `passTreeSym` follows; `never_halts_of_open`: the open question as two questions | `blank_halt_open_of` with `clean_tree_small_step` (or `clean_small_step_kernel`) and `entry_small_halt`; nothing evaluated |
| `BB6/WideEntry.lean` | `EntryWide`: the loop entry has W ≤ 32R; `wideEntryOK_sound`: checked on a class of one coordinate at every point of its cone; `cleanWideOK`: `cleanSmallOK` and that; `EntryFar`, `farEntryOK_sound`, `cleanFarOK`: the same for 15W ≤ 64(W − b) and 15W + 26 ≤ 32(W − b + R) | proved, standard axioms |
| `thm/CleanWideTheorem.lean`, `thm/CleanWideMass.lean` | `clean_tree_wide_step`: as `clean_tree_small_step`, with `cleanTreeGW Γ d` and entries that also satisfy `EntryWide`; `clean_tree_wide_cut_mass`: at 36 digits over the widths ≥ 2⁴¹ the same counts as `cleanTreeGS` | the proved explorer, nothing evaluated; the counts by `exploreMassWE` and `native_decide`, used by no theorem about the machine |
| `thm/CleanFarTheorem.lean`, `thm/CleanFarMass.lean` | `clean_tree_far_step`: the same with `cleanTreeGF Γ d` and entries that satisfy `EntryFar`; `clean_tree_far_cut_mass`: again the counts of `cleanTreeGS` | as for the wide entries |
| `thm/WideHalt.lean` | `step_wide`, `LoopChain.wide_end`: from a pass start with W ≤ 64R + 6 and, if W ≡ 2 (mod 4), W ≤ 32R, every pass start of the loop's chain has W ≤ 64R + 6 or 15W ≤ 64(W − b) (`WideShape`), so W ≤ 32(W − b + 2R) + 6 (`wideShape_bound`; on a lane W − b + 2R + 22 = 2^m, W ≤ 2^(m+5) + 6, `wideShape_pow2`); `entry_wide_halt`; `blank_halt_open_wide`, `blank_halt_open_wide_kernel`, `never_halts_of_wide`: `blank_halt_open_small` and the open question with the shape at the pass start; `openHaltFams_wide`, `reentryFams_wide`: the eight families have the shape only below width 58,502, the 21 at larger scales only below 2³⁵; `blank_halt_not_family`: the run from blank tape halts through none of them | the steps' maps (`StepMap`) and the gaps by `omega`, the families' R and W − b by `decide`; `blank_halt_open_of` with `clean_tree_wide_step` (or `clean_wide_step_kernel`) and `entry_wide_halt`; nothing evaluated |
| `BB6/BigEnd.lean` | `NoEndBelow N`, `endOK N`, `endOK_sound`, `endCert N`: `NoSmallAt`, `smallOK` and `smallCert` for the right ends below N; `EntryBigEnd N`, `bigEntryOK N`, `bigEntryOK_sound`: `EntryNoSmall` and its check with N for 178 and a width of at least 2⁴¹; `cleanBigOK N`: `cleanEntryOK`, `bigEntryOK N` and `farEntryOK` | proved, standard axioms |
| `thm/CleanBigTheorem.lean`, `thm/CleanBigMass.lean` | `clean_tree_big_step`: as `clean_tree_far_step`, with `cleanTreeGB Γ d` and entries that satisfy `EntryBigEnd 769` for `EntryNoSmall`; `clean_tree_big_cut_mass`: again the counts of `cleanTreeGS` | as for the wide entries |
| `thm/FarHalt.lean` | `step_far`, `LoopChain.far_end`: a full pass and a round-7 break land with 15W′ ≤ 64(W′ − b′), a half pass when 15E + 26 ≤ 32(E − b + R), so from a pass start with 15W ≤ 64(W − b) and that every pass start of the chain has 15W ≤ 64(W − b) (`FarShape`; on a lane W − b + 2R + 22 = 2^m, 15W + 128R + 1,408 ≤ 2^(m+6), `farShape_pow2`); `entry_far_halt`; `blank_halt_open_far`, `blank_halt_open_far_kernel`, `never_halts_of_far`: `blank_halt_open_wide` and the open question with that shape | as for `thm/WideHalt.lean` |
| `thm/BigEndHalt.lean` | `noEnd_full`, `noEnd_end`, `break7_noEnd769`, `LoopChain.big_end`: a full pass keeps `NoEndBelow N`, a round-7 break from a width of at least 2⁴¹ lands with it for N = 769, so from a start of width at least 2⁴¹ with `NoEndBelow 769` (and after its half pass) the chain ends at R ≥ 769; `entry_big_halt`; `blank_halt_open_big`, `never_halts_of_big`: `blank_halt_open_far` and the open question with R ≥ 769 too | as for `thm/WideHalt.lean` |
| `thm/CleanEntryMass.lean`, `thm/CleanEntryKernelMass.lean` | `clean_tree_entry_cut_mass`, `clean_entry_kernel_cut_mass`: the leaf counts and measures of `cleanTreeGE 2⁴¹ 36` and `cleanTreeGE 2²⁴ 36` | `exploreMassWE`, `native_decide`; used by no theorem about the machine |
| `BB6/MassPar.lean` | `massPrefix_eq`: the tally of `exploreMassWE` is that of the leaves above a split level plus the tallies of the nodes on it; `massPar_eq`: the same with the nodes' tallies computed as parallel tasks | proved, standard axioms |
| `thm/CleanEntryMass40.lean`, `thm/CleanEntryMass44.lean` | `clean_tree_entry_cut_mass40`, `clean_tree_entry_cut_mass44`: the leaf counts and measures of `cleanTreeGE 2⁴¹ 40` and `cleanTreeGE 2⁴¹ 44` | `massPar` (`massPar_eq`), `native_decide`; used by no theorem about the machine |

## Why a one-variable tree over clean tapes, and not the two-marker route tree

The route tree (`ROUTE_TREE.md`) starts from two-marker states G 1, M m, M E − 2 with both gaps at least Γ. Chaining
it along the machine's run does not work: the machine's own run reaches two-marker states with a tiny first gap again
and again (for example m = 56 at width 34,478,025, m = 152 at width 12,260,337), which no cone of large gaps contains.
Clean tapes have one number, the width W, and every position on the way to the next clean tape is an affine function
of it, so the cone is just W ≥ Γ, and the clean tapes the run reaches are all wider than the first one. This is the
class tree of the exhaustive check (`../csearch/nrefdfs2.c`), proved: a split on the next binary digit of W/2 when a
round is not decided, and a path stops at the first wider clean tape.

## The clean-tape tree

The tree is built by the proved explorer, so `clean_tree_step` and the end-to-end theorems hold at every depth and
evaluate nothing; the depth only decides how many classes are cut. The cut classes, evaluated (`RouteStats.lean`, and
`thm/CleanMass.lean`, `thm/CleanMass40.lean`, `thm/CleanDirectMass.lean`, `thm/CleanDirectMass40.lean` and
`thm/CleanKernelMass.lean` for 36 and 40 digits), are the same for the trees with the cones W ≥ 2²⁰
(`cleanTreeG 2²⁰ d`, used by the kernel-only theorems), W ≥ 2³² (`cleanTree d`) and W ≥ 2⁴¹ (`cleanTreeG 2⁴¹ d`,
used above the direct runs):

| depth | closed | cut | cut measure | exhaustive check, open classes |
|---|---|---|---|---|
| 20 | 1,850 | 1,930 | 1.8 × 10⁻³ | 1,930 |
| 24 | 9,814 | 10,722 | 6.4 × 10⁻⁴ | 10,722 |
| 28 | 52,599 | 57,934 | 2.2 × 10⁻⁴ | 57,934 |
| 32 | 276,729 | 303,560 | 7.1 × 10⁻⁵ | 303,560 |
| 36 | 1,507,376 | 1,660,024 | 2.4 × 10⁻⁵ | 1,660,024 |
| 40 | 8,107,588 | 9,188,898 | 8.4 × 10⁻⁶ | 9,188,898 |

The cut classes are the exhaustive check's open classes (`../dfs/merged56_fixed.txt`; compared class by class at 36
and 40 digits), and every cut leaf is at full depth: a path is cut only when it has made d splits without reaching a
wider clean tape, with a residue split still to make. The cut classes grow about 1.52-fold per digit, as the open
classes of the exhaustive check do (1.53), so the cut measure falls about 0.76-fold per digit. Longest path at 36
digits: 59 rounds. Every clean leaf is a one-marker clean tape decided to be wider than the start (`exploreW` stops
only where `symClean1` and `widerB` hold, which is what `RTree.okW` checks).

**The edge of the cone.** The cone W ≥ Γ is a condition over the rationals, and a class of W/2 modulo 2^k is compared
at the cone's corner, which can lie between two of its members. A comparison can then be undecided on the class
although it comes out differently only for the smallest member, or only below it. At depth 31, for example, the class
W = 2 + 2³²z (z ≥ 1) has after 30 rounds the marks M 4z, M 5 + 268,435,464z, W 59 + 2,281,701,380z, and the round
asks whether the first marker is exactly 3 cells right of the gap: 4z = 4, true only for the smallest member,
W = 2³² + 2. In the class W = 2⁴⁰ + 2 + 2⁴¹z of the tree with the cone W ≥ 2⁴¹ the marker is at 2 + 4z after 39
rounds, and 2 + 4z = 4 is false for every member but true at z = 1/2, which the cone contains. A residue split cannot
separate the smallest member from the others, so such a class, left as it is, stays cut at every depth, and the edge
moves with the cone: 7 such classes at 36 digits with the cone W ≥ 2³², 2 at 40 digits with the cone W ≥ 2⁴¹, 1,074
at 36 digits with the cone W ≥ 2²⁰ (from depth 19, one below the cone's exponent, where the same pair carries
2 · 2⁻¹⁹ of measure). The clean tapes left open at every depth would then not be a set of measure zero.

The exhaustive check keeps an exact integer threshold for each comparison and runs the members below it directly. The
explorer does the same with a `drop` node (`BB6/CleanTree.lean`): where a round is undecided and no residue split
decides it, it runs the class's smallest member with the mark model to a wider one-marker clean tape (`toWider`, at
most 10,000 rounds), and goes on with the rest of the class under the cone that starts at the next member, a corner
that is itself a member. `RTree.okW` checks a drop (`dropOK`: a cone form excludes the members below, the forms do not
depend on the unused coordinate, and the direct run reaches a wider clean tape), `RTree.soundW` covers it, and `cutMem`
counts the dropped member as not cut, so the theorems keep their form. A class drops at most `cleanDrops` = 4 members
before it is split or cut, each split's children starting afresh (the clean tapes W = 2ʲ + 2 need a drop at every
level). The trees drop 20 members at 36 digits with the cone W ≥ 2³² (W = 2ʲ + 2 for j = 32 to 37, W = 3 · 2ʲ + 2 for
j = 31 to 36, and 8 others), 72 at 40 digits; 2 at 40 digits with the cone W ≥ 2⁴¹ (W = 2⁴¹ + 2, after which its class
stays open at depth 40 with a residue split to make, as in the exhaustive check, and W = 3 · 2⁴⁰ + 2, after which its
class closes); and 1,599 at 36 digits with the cone W ≥ 2²⁰, from W = 2²⁰ + 2 up. No class needs more than 2.

## Clean tapes below 2⁴¹, one by one

The exhaustive check (`../csearch/nrefdfs2.c`) covers the small members of its open classes by running them, up to
2⁶¹. `BB6/CleanRange.lean` does the same in Lean: `directOK W` runs the mark model from the clean tape of width W for
at most 10,000 rounds, until a one-marker clean tape wider than W (`toWider`, the run a drop makes), and
`directOK_sound` turns a run that gets there into a statement about the machine. `RTree.cuts1` lists the cut classes of a clean-tape tree as residues of W/2
modulo powers of two, `rangeOK lo hi t` runs every member of every cut class with lo ≤ W < hi, and `rangeOK_sound`:
every clean tape of width in [lo, hi) that the tree leaves open passes `directOK`. `thm/CleanDirect.lean` evaluates
`rangeOK 2³² 2⁴¹ (cleanTree 36)` with `native_decide` (26,508,327 clean tapes in the 1,660,024 cut classes, each run
to a wider one in at most 127 rounds), and with `clean_tree_step` for the other clean tapes, `clean_step_direct`:
every clean tape of width in [2³², 2⁴¹) reaches a wider one. `blank_halt_clean_from` (`thm/EndToEnd.lean`) is the chain for any such bound B,
with the tree over the widths ≥ B above it, and `blank_halt_clean_direct` is the case B = 2⁴¹.

## The clean tapes' loop entries

On its way from one clean tape to the next, the run may reach a phase-0 pass start, and the clean-tape tree then
follows the loop's passes round by round, splitting on the digits of W/2 that each pass consumes, until its depth runs
out. `cleanTreeGE Γ d` (`thm/CleanEntryTheorem.lean`, built by `RTree.exploreWE`, `BB6/CleanEntryTree.lean`) is the
same exploration, except that it stops a path at the first round start that passes `cleanEntryOK`: the route tree's
entry check (`entryOK`, `ROUTE_TREE.md`), decided on the whole class, and the entry decided to be wider than the
start. The check asks for a phase-0 pass start with every gap at least 448, width at least 2²⁴ and, when W ≡ 2
(mod 4), the middle wall at least 896 below the width, from which no member of the class closes through the loop
(`EntryNoClose`): after p full passes a close needs R = 16^p·r with r in the closing set and L₁ = 64^p·ℓ with ℓ in r's
class and ℓ ≡ 3 (mod 7), and the check bounds L₁ by R on the cone, so that beyond a computed P only ℓ = 0 fits, and
shows that every candidate below P misses the class's integer points (on these classes of one coordinate R = 16^p·r
fixes the point directly, `solveOut1`). Where the check fails, the path goes on as in `cleanTreeG Γ d`, so the cut
classes of `cleanTreeGE Γ d` are among those of `cleanTreeG Γ d`.

From such an entry the loop's chain reaches no closing class (`EntryNoClose.no_close`: from a width ≥ 2²⁴ a close is
p full passes after at most one half pass, `LoopChain.close_wide`, and the check excludes both), and with the
middle-wall condition every landing of the chain is again a pass start with every gap at least 448 (`landing_wide`).
So a halt from the entry needs the chain to end where the run, close-free, leaves phase 0 or the halving chain at a
round start that is not three walls, and a stuck configuration after that (`entry_halt`, from `loop_halt_leaves`).

`clean_entry_chain` chains the clean tapes as `clean_chain` does, by strong induction on the halting time, with what a
halt from a loop entry needs as a hypothesis: for each entry and each halting time, either a property `Q` of the entry
and the time left, or a wider clean tape of even width that the run reaches from the entry after at least one step,
from which the chain goes on. `blank_halt_clean_entry_from` takes `Q` from `entry_halt`, so there the entries end the
chain. A theorem that follows the run from where the loop's chain ends to the next clean tape (or into classes of its
own) fits the second alternative and carries the chain on through the entries.

The cut classes (untrusted survey with the same explorer; `thm/CleanEntryMass.lean` evaluates the tree that
`blank_halt_clean_entry` uses):

| cone | depth | clean | cut (without entries) | cut measure | entries | entries' measure |
|---|---|---|---|---|---|---|
| W ≥ 2³² | 32 | 220,290 | 236,213 (303,560) | 5.5 × 10⁻⁵ | 5,423 | 1.34 × 10⁻³ |
| W ≥ 2³² | 36 | 1,163,106 | 1,256,031 (1,660,024) | 1.83 × 10⁻⁵ | 28,639 | 1.34 × 10⁻³ |
| W ≥ 2⁴¹ | 36 | 1,163,068 | 1,255,963 (1,660,024) | 1.83 × 10⁻⁵ | 28,660 | 1.34 × 10⁻³ |
| W ≥ 2²⁴ | 36 | 1,169,027 | 1,263,032 (1,660,024) | 1.84 × 10⁻⁵ | 28,382 | 1.33 × 10⁻³ |

The entries take a quarter of the cut classes away at both depths, and the entries' measure hardly changes from 32 to
36 digits: nearly all of them are met within the first 32 splits. The cut classes still grow about 1.52-fold per
digit, as without entries: none of the cut classes' runs meets a three-wall round start within the depth (at 32 and
36 digits over the widths ≥ 2⁴¹, `EntryStats.lean`), so what is left are the runs that stay outside the loop. Over the
widths ≥ 2²⁰ the entries' width test (2²⁴) is decided on few classes (246 entries at 36 digits), so
`blank_halt_clean_entry_kernel` uses the plain tree over the widths ≥ 2²⁰ below 2²⁴ and the tree with entries over the
widths ≥ 2²⁴ above (`thm/CleanEntryKernelMass.lean` evaluates the latter); `clean_entry_chain` takes the step at each
width as a hypothesis, so the two trees fit in one chain.

## Past the loop's end, from blank tape

`clean_entry_chain` takes what a halt from a loop entry needs as a hypothesis. `pass_halt_chain` (`thm/PassHalt.lean`,
"From a pass start to the next checkpoint", above) gives it. A loop entry that cannot close is a pass start of width at
least 2²⁴ with every gap at least 448, and with the middle wall at least 896 from the end when W ≡ 2 (mod 4). From
there a halt follows the loop's chain to a last pass start where L₁ is in a closing class, or that lies in a cut leaf
of its pass-start tree at every depth, or from which the run reaches a wider clean tape of even width and halts from
there. At such an entry the first is out (`EntryNoClose.no_close`), so a halt from the entry needs a pass start cut at
every depth, reached along the chain, or a wider clean tape (`entry_pass_halt`), and `clean_entry_chain` goes on from
the clean tape. `blank_halt_pass_from` puts the two together for a prefix and the steps of a clean-tape tree:
`blank_halt_pass` with the prefix to 2³², the direct runs to 2⁴¹ and `cleanTreeGE 2⁴¹ d`, and `blank_halt_pass_kernel`
with the kernel's prefix to 2²⁰, `cleanTreeG 2²⁰ d` below 2²⁴ and `cleanTreeGE 2²⁴ d` above
(`clean_entry_step_kernel`).

So every part of a halting run from blank tape is followed: from clean tape to clean tape by the clean-tape tree, into
the loop at the entries, through the loop by its chain, and past the loop's end by the pass-start trees, to the next
landing of the chain or a wider clean tape. What is left are two kinds of cut classes. The clean-tape tree's have
measure 1.83 × 10⁻⁵ at 36 digits, and their number grows about 1.52-fold per digit, so their measure shrinks with depth.
The pass-start trees' are 2.0% of a start class at 20 splits for R < 178 and 3.8% for R ≥ 178. Those for small R do not
shrink to nothing, since some of them are real halts (1/8 of the pass starts with R = 6, `pass_r6_halt`), so no depth of
the pass-start trees can show that their cut classes do not halt. What `blank_halt_pass` leaves open is whether the run
from blank tape reaches one of the pass starts that halt, or a clean tape of the cut classes.

The pass starts the run can reach this way are the last pass starts of loop chains from the clean-tape tree's
entries. At each of those entries the right end R is affine in the class's coordinate with a nonzero coefficient, never
constant: all 28,660 entries at 36 digits over the widths ≥ 2⁴¹, 25,058 of them (99% of the entries' measure) with a
coefficient of 2-adic valuation 2 (`EntryStats.lean`, untrusted). A full pass, R → R/16 on the subclass where 16
divides R, keeps R so. So a chain from an entry ends at R₁ < 178 only at isolated members of the entry's class, and
apart from those the pass starts it reaches are in the tree for R ≥ 178, whose cut classes fall from 8.8% of a class
at 16 splits to 3.8% at 20 and 1.6% at 24, with no decided halt among them. The next section shows that there are no
such isolated members: the chain from a loop entry never ends below 178.

## No small right end past the loop

The trees for R < 178 are where the pass starts that halt live: the halting classes (`pass_class_halt`, among them 1/8
of those with R = 6, `pass_r6_halt`), and every round the model left uncovered in a sample of 1,000 random pass starts
per R came for R in {4, 6, 8, 16, 32, 48, 64}. `thm/SmallEndHalt.lean` shows that the run from blank tape ends no loop
chain at one of them past a loop entry: the loop's chain from an entry ends at a right end R ≥ 178.

A run of full passes divides R by 16 and the left countdown L₁ by 64, so it ends at a right end r < 178 only if
R = 16^p·r and L₁ = 64^p·ℓ, with ℓ ≡ 3 (mod 7) as every left countdown is (64 ≡ 1 mod 7); `NoSmallAt R L₁` says this
never happens (`BB6/SmallEnd.lean`). It holds whenever R³/L₁² > 177³/9 (`noSmall_sigma`): full passes keep R³/L₁²
(16³ = 64²), and at r < 178 with |ℓ| ≥ 3 it is r³/ℓ² ≤ 177³/9. A full pass keeps `NoSmallAt` (`noSmall_full`). A
round-7 break resets it: from a pass start of width E ≥ 2³⁷ it lands with 32R′ ≥ S = 3E + 5R and 0 < 96L₁′ ≤ 385S
(the bounds of `break7_sigma`), so R′³/L₁′² ≥ S/527,023 > 177³/9 (`break7_noSmall`; S ≥ 3 · 2³⁷ is enough, 2³⁶ is
not). A half pass is only ever the first step. So from a pass start of width ≥ 2³⁷ with `NoSmallAt` for its own R and
L₁ and, when W ≡ 2 (mod 4), for those after a half pass, every pass start of the chain has `NoSmallAt`, and the last
one, with p = 0, has R ≥ 178 (`LoopChain.small_end`).

At a loop entry of the clean-tape tree R and L₁ are affine in the class's coordinate z, and R³/L₁² grows like z.
Untrusted, at 36 digits over the widths ≥ 2⁴¹: R³/L₁² > 177³/9 at every member of 28,516 of the 28,660 entries; the
other 144 (0.11% of the entries' measure) fall short only at widths below 2⁴³·⁵ (933,158 members in all), where the
σ bound alone does not decide. The check decides every member exactly instead (`smallOK`, on a class of one
coordinate, as `exclOK` does for the closing classes): for each p below a bound P and each r < 178, R = 16^p·r fixes
z, which must not be an integer point of the cone with 64^p dividing L₁ there (`smallPt1`); past P the bounds
α·R + α₀ ≤ L₁ ≤ β·R + β₀ on the cone (those of `exclCert`) leave only ℓ = 0, which no left countdown is
(`smallOK_sound`). `smallEntryOK` asks this for the full passes from the entry and, unless W ≡ 0 (mod 4) on the class,
after a half pass, with the entry's width at least 2³⁷ (`EntryNoSmall`, `smallEntryOK_sound`).

`cleanTreeGS Γ d` (`thm/CleanSmallTheorem.lean`) is `cleanTreeGE Γ d` with the entry test `cleanSmallOK`
(`cleanEntryOK` and `smallEntryOK`), built by the same proved explorer, so `clean_tree_small_step` holds at every depth
with nothing evaluated; where the check fails, the path goes on as in the plain tree. At 36 digits over the widths
≥ 2⁴¹ it never fails: the tree has the same 1,255,963 cut classes, 1,163,068 clean leaves and 28,660 loop entries as
`cleanTreeGE directWidth 36` (`thm/CleanSmallMass.lean`). `entry_small_halt` is `entry_pass_halt` with R₁ ≥ 178, and
`blank_halt_small_from` chains it as `blank_halt_pass_from` does (`clean_entry_chain_of`: `clean_entry_chain` for any
property of the entries). So `blank_halt_small`: a halt from blank tape needs a clean tape of width ≥ 2⁴¹ cut at
every depth of `cleanTreeGS 2⁴¹ d`, or a pass start wider than 2⁴¹ with R ≥ 178 cut at every depth of
`passTreeSym d`. The loop's chain ends in none of the trees for R < 178, with their halts. `blank_halt_small_kernel`
is the same from the kernel's prefix to 2²⁰, with the plain tree below 2³⁷ and `cleanTreeGS 2³⁷ d` above
(`clean_small_step_kernel`).

## The open clean tapes come first

`blank_halt_clean_direct` and `blank_halt_pass` follow the same halting run from blank tape with two trees over the
clean tapes: `cleanTreeG 2⁴¹ d`, which follows the run through the loop round by round, and `cleanTreeGE 2⁴¹ d`, which
stops at the loop entries that cannot close. Where a path of the second ends at an entry, the same path of the first
goes on, so a clean tape that the first tree resolves at some depth reaches a wider clean tape, whatever the second
does with it. `clean_entry_chain_open` is `clean_entry_chain` in that order: at each clean tape it takes the step of
the plain tree where that tree does not cut the clean tape at every depth, and the step of the tree with entries
otherwise, and when that step ends at a loop entry it records that the plain tree left the clean tape open at every
depth. With `entry_pass_halt` at the entries this gives `blank_halt_open`: the run reaches a clean tape of width
≥ 2⁴¹ that `cleanTreeG 2⁴¹ d` leaves open at every depth, and either `cleanTreeGE 2⁴¹ d` leaves it open at every depth
too, or the run from it passes a loop entry and reaches a pass start that its pass-start tree leaves open at every
depth. So the open pass starts are not a second open set beside the open clean tapes; they come after them. At 36
digits the clean tapes that both trees leave open are the 1,255,963 classes of measure 1.83 × 10⁻⁵, and those that only
the plain tree leaves open, which meet a loop entry in the other, are the remaining 404,061 of its 1,660,024 classes
(5.9 × 10⁻⁶).

From such an entry the pass starts the run reaches are not spread over the four coordinates of the pass-start trees:
they form a family of one coordinate, the entry's class of W/2. Every landing of the loop's chain also lies on one
plane, 2(b − a) = W − 2R − 6 (`landing_plane`, from the step's maps on L₁ and on the first wall). `ReachStats.lean`
(untrusted) roots the pass-start explorer at each loop entry of `cleanTreeGE 2⁴¹ d`, in the clean tape's own
coordinate, and follows the run past each landing of the chain to a wider clean tape. Over the 1,845 entries at 28
digits (0.13% of the clean tapes), the part of the entries' measure that is still cut falls from 13.5% at 8 more splits
to 4.6% at 12 and 1.5% at 16 (and over the 24 entries at 20 digits to 0.51% at 20), where the tree over all pass starts
with R ≥ 178 keeps 8.8% at 16 and 3.8% at 20. About 0.3% of the entries' measure lands once on the way, and almost none
twice. Followed this way, the entries' runs are resolved about as well as `cleanTreeG` resolves them with the digits it
has left at 36 digits (0.44% of the entries' measure open), which is why `blank_halt_open` takes that tree first.

`clean_entry_chain_open` and `blank_halt_open_of` take the test of the loop entries as a parameter, so the same order
works with the small-end check: with `cleanTreeGS` as the tree with entries and `entry_small_halt` at them,
`blank_halt_open_small` (`thm/OpenSmallHalt.lean`) puts the pass start that may come after an open clean tape in the
tree for every R ≥ 178. What is left is two questions (`never_halts_of_open`): does the machine halt from a clean tape
that both trees leave open at every depth, and does it halt from a pass start with R ≥ 178 that `passTreeSym` leaves
open at every depth and that the run reaches from a clean tape that `cleanTreeG` leaves open at every depth. In the
second, the reaching is what matters: such pass starts that halt exist at every width (`sym_open_halt`,
`open_halt_families`) and at every scale of the third gap tried (`reentry_open_halt`), and the loop's chain can land on
one after a full pass (`full_pass_open_halt`).

## The pass starts a halt needs are wide

The eight families of `open_halt_families` and the 21 of `reentry_open_halt` are pass starts with R ≥ 178 that halt at
every width, and a full pass of the loop's chain lands on the eighth (`full_pass_open_halt`). `thm/WideHalt.lean` shows
that the run from blank tape reaches none of them: the loop's chain from a loop entry of the clean-tape tree ends at a
pass start of a shape that each family has only below width 2³⁵.

Each step of the chain from a pass start (b, E, R) with every gap at least 448 (so b ≤ E − R − 449) lands where its map
puts it (`StepMap`, with L₁ = 147b − 112E + 392R − 186 for walls at a, b and E − R − 1, `passL1_www`):

| step | W′ | R′ | b′ | so the landing has |
|---|---|---|---|---|
| full pass | E + 24 | R/16 | (b + 48E − 8R + 1,250)/64 | 64(W′ − b′) = 16E − b + 128R′ + 286 ≥ 15E + 144R′ + 735: 15W′ ≤ 64(W′ − b′) |
| half pass, from E ≡ 2 (mod 4) | E + 6 | R/2 | (b + E − R + 10)/2 | W′ ≤ 64R′ + 6 if E ≤ 32R |
| round-7 break | E + 24 | (4E + 4R − b + 110)/32 | (3b + 16E − 6R + 446)/32 | 32R′ ≥ 3E + 5R + 559: W′ ≤ 64R′ + 6 |

A family has R = R₀ and W − b = D₀ fixed, with the width and the middle wall moved together by multiples of 2^k. Solved
for the start, a full pass lands on (W₀ + 2^k t, R₀, b₀ + 2^k t) only from R = 16R₀, E = W₀ − 24 + 2^k t and
b = 64b₀ − 48W₀ + 128R₀ − 98 + 2^(k+4) t, a round-7 break only from E = W₀ − 24 + 2^k t and
b = 4E + 4R − 32R₀ + 110, and a half pass only from R = 2R₀, E = W₀ − 6 + 2^k t and E − b = 2(D₀ − R₀ − 1). The
start's gaps bound the width: a full pass lands on the family only at W′ ≤ (64D₀ − 144R₀ − 375)/15 and a round-7
break only at W′ ≤ (32R₀ − 487)/3; a half pass, only ever the first step (every landing has W ≡ 0 mod 4), starts from
a loop entry with R = 2R₀. The loop entries of the clean-tape tree are early: at 36 digits over the widths ≥ 2⁴¹,
R > W/29.02 and W − b > 0.455W at every member of each of the 28,660 entry classes (`EntryForms.lean`, untrusted).
`EntryWide` asks W ≤ 32R at the entry, and `cleanWideOK` (`BB6/WideEntry.lean`) adds it to the entry test
`cleanSmallOK`. `cleanTreeGW Γ d` (`thm/CleanWideTheorem.lean`) is the clean-tape tree with that test, built by the
proved explorer, so `clean_tree_wide_step` holds at every depth with nothing evaluated; at 36 digits over the widths
≥ 2⁴¹ it has the same 1,255,963 cut classes, 1,163,068 clean leaves and 28,660 loop entries as `cleanTreeGS`
(`thm/CleanWideMass.lean`).

An entry with W ≤ 32R has W ≤ 64R + 6 itself, so by the table every pass start of its chain has the shape

    W ≤ 64R + 6  or  15W ≤ 64(W − b)      (`WideShape`, `step_wide`, `LoopChain.wide_end`),

and so W ≤ 32(W − b + 2R) + 6 (`wideShape_bound`). `entry_wide_halt` is `entry_small_halt` with the shape at the
chain's last pass start, and `blank_halt_open_wide` is `blank_halt_open_small` with `cleanTreeGW` and the shape. The
eight families have R₀ ≤ 914 and D₀ ≤ 3,702, so a member has the shape only if W ≤ 64R₀ + 6 ≤ 58,502 or
15W ≤ 64D₀ ≤ 236,928 (`openHaltFams_wide`); the 21 have R₀ = 178 and D₀ = 2^(j+2) − 378 < 2³², so only if
W ≤ 11,398 or 15W ≤ 64D₀ < 2³⁸, below 2³⁵ (`reentryFams_wide`). The pass start a halt needs is wider than 2⁴¹: the run
from blank tape halts through none of them (`blank_halt_not_family`).

The bound holds whatever the route from the pass start to the halt. On the main route the run meets the end off the
chain at x = (W − b + 2R + 14)/4 and halves to 0 from there, which needs x = 2^j − 2 or 3 · 2^j − 2, so Q = W − b + 2R +
22 = 2^m or 3 · 2^m (m = j + 2); four of the eight families are on it (R₀ = 178, 466, 474 and 186, x = 254, 510, 510 and
1,022), as are the 21 (x = 2^j − 2, j = 10 to 30), and the other four meet the end one to four more times before the
halving starts. On a lane Q = 2^m the shape needs W ≤ 2^(m+5) + 6 (`wideShape_pow2`), so a halt on the main route past a
pass start wider than 2⁴¹ needs m ≥ 36, and each lane holds only pass starts below 2^(m+5). No residue keeps the run off
the lanes: along each entry class Q is affine in the class's coordinate z, Q = q₀ + q₁z with q₁ of 2-adic valuation 1 to
7, and c · 2^n = q₀ + q₁z has a solution exactly when c · 2^n ≡ q₀ (mod q₁), which for q₁ = 2^v·u (u odd) fixes n modulo
the order of 2 mod u. But solutions are rare: over the 28,660 entry classes and every chain shape that the steps'
divisibility admits on them (an optional half pass, then up to three full passes or round-7 breaks: 42,187 pairs), Q =
2^n or 3 · 2^n with n < 4,096 has two solutions in the cone, both at an entry itself: Q = 2¹⁷² at width about 2^171.3
and Q = 3 · 2⁹² at width about 2^93.3. Run in the mark model (`RunWalls.lean`), neither meets the end at x, and both
reach a wider clean tape, in 8 and 19 rounds (untrusted, `../notes/LAB_NOTES.md`).

The halts close through a re-entry into the loop, and that is where the shape tells (untrusted, `../runs/reentry.py`).
On the main route with R ≡ 2 (mod 8), round 9 is a pass start with R′ = Q/32, a half pass takes it to round 11 with
R′ = Q/64 = 2^(j−4) and L₁′ = (49 · 2^(j+3) + 441R − 7W + 3,582)/256 (exact at 498 runs of the model across scales 10
to 33), and full passes take it down to the halting class. That chain ends below 178 only if R′³/L₁′² ≤ 177³/9
(`noSmall_sigma`). With the shape, |L₁′| is at most about 2^(j+2), and over every pass start of a lane with the shape
and width ≥ 2⁴¹ (j ≥ 35) R′³/L₁′² is at least 1.9 × 10⁶ > 177³/9 = 616,137: the main route gives no halt at a pass
start a halt from blank tape needs. This covers R ≡ 2 (mod 8) only. With R ≡ 6 (mod 8) the three-wall start at round 7
has R′ = Q/16 and is not a round-7 break of the loop's chain (that needs 32R′ = 4W − b + 4R + 110), and it and the
other routes re-enter with their own forms, which need the same check (next section).

## The middle wall is far from the end

The first case of the wide shape, W ≤ 64R + 6, comes from the half pass and the round-7 break, and both land in the
second case too. A round-7 break lands with 32b′ = 3b + 16E − 6R + 446, so 64(W′ − b′) − 15W′ = 17E − 6b + 12R + 284,
which is positive since b < E: its middle wall is near the middle of the tape. A half pass lands with
2(W′ − b′) = E − b + R + 2, so with 15W′ ≤ 64(W′ − b′) when 15E + 26 ≤ 32(E − b + R). `EntryFar` asks both at the loop
entry, 15W ≤ 64(W − b) for a chain with no step and 15W + 26 ≤ 32(W − b + R) for a half pass, and `cleanFarOK`
(`BB6/WideEntry.lean`) adds it to `cleanSmallOK`; the 36-digit entries have W − b > 0.4558W and R > W/29.02, and
`cleanTreeGF` (`thm/CleanFarTheorem.lean`) has the same counts as `cleanTreeGS` there (`thm/CleanFarMass.lean`). So
the chain's last pass start has

    15W ≤ 64(W − b)      (`FarShape`, `step_far`, `LoopChain.far_end`, `blank_halt_open_far`),

and on a lane Q = 2^m, 15W + 128R + 1,408 ≤ 2^(m+6) (`farShape_pow2`): past 2⁴¹, m ≥ 39.

With this shape the halting routes found so far are out of reach, untrusted. The halting-classes census (every even
R from 178 to 198 and W − b from R + 449 to 8,192: 72 closing classes, `../notes/LAB_NOTES.md`) finds eight routes.
Each reaches a three-wall round start P′ with the phase-0 parities, whose right end R′ and left countdown L₁′ are affine
in (b, W, R) on the route's class (a symbolic run with b, W − b and R free, checked on the model). On every route but
B, every step from P′ is an exact full pass, straight to a pass start in a class of `pass_class_halt` with r = 4, 8,
16, 32 or 48:

| route | R mod 8 | P′ at round | lane | R′ | L₁′ |
|---|---|---|---|---|---|
| A (main) | 2 | 11 | Q = 2^(j+2) or 3 · 2^(j+2) | Q/64 | (91W − 98b + 637R + 5,738)/256 |
| A2 | 2 | 11 | 2Q − R + 6 = 2^(j+3) or 3 · 2^(j+3) | (2Q − R + 6)/128 | (91W − 245b + 441R + 4,562)/256 |
| A3 | 2 | 11 | 3Q + 76 = 2^(j+4) | (3Q + 76)/256 | (−308W − 441b + 1,176R + 13,534)/512 |
| B | 4 | 2 | the loop's half pass | R/2 | (147b − 77W + 245R − 246)/2 |
| C | 6 | 7 | Q = 2^(j+2) | Q/16 | (140W − 49b + 392R + 4,366)/32 |
| C2 | 6 | 7 | 3Q + 76 = 2^(j+4) | (3Q + 76)/64 | (385W + 441b + 10,834)/32 |
| C3 | 6 (R = 182) | 7 | Q + 36 = 2^(j+2) or 3 · 2^(j+2) | (Q + 36)/32 | (−840W + 343b + 343R + 740)/32 |
| C4 | 6 (R = 198) | 11 | Q + 36 = 2^(j+2) or 3 · 2^(j+2) | (Q + 36)/128 | (−504W − 245b + 784R + 8,438)/512 |

Route B is a step of the loop's chain, so the chain's last pass start is not on it. On the others, full passes keep
R′³/L₁′² (R → R/16 and L₁ → L₁/64 exactly), and every left countdown is ≡ 3 (mod 7), so ending at a right end r takes
R′³/L₁′² = r³/ℓ² ≤ r³/9, with r fixed by R′ = 16^p · r; below 178 at all, 177³/9 (`noSmall_sigma`). On a lane, R′ is
fixed and the pass starts with every gap at least 448, width at least 2⁴¹ and the shape form a polygon in (R, W), so
the least R′³/L₁′² is at a corner (`../runs/reentry.py sigma`, over every lane value c · 2^n with c = 1 or 3):

| route | least R′³/L₁′², wide shape | lanes at or below r³/9 | least R′³/L₁′², 15W ≤ 64(W − b) | lanes at or below r³/9 |
|---|---|---|---|---|
| A | 1.78 × 10⁶ | 0 | 6.79 × 10⁶ | 0 |
| A2 | 1,915 | 0 | 8.09 × 10⁵ | 0 |
| A3 | 243 | 2 | 30,560 | 0 |
| C | 7,879 | 1 | 7.19 × 10⁵ | 0 |
| C2 | 47 | 4 | 6,099 | 0 |
| C3 | 38 | 5 | 2,831 | 0 |
| C4 | 70 | 3 | 7,893 | 0 |

With the far shape no lane of any route reaches its end's bound, and those of A, A2 and C stay above 177³/9 too: a pass
start a halt from blank tape needs is on none of these routes. It rests on the routes' forms, which are observed on the
model, not proved, and it covers these eight routes only. A census for R from 200 to 262 (W − b ≤ 4,096) finds more.
Most of its classes reach a three-wall start P′ and go on to a class of `pass_class_halt`, as here, and need their forms
checked the same way; but at R = 230 four classes (W − b = 1,570 three times and 3,618 once) reach no three-wall round
start after round 0 and close by the halving alone, and two (W − b = 738) land at round 13 in the R = 6 class
(`thm/PassHaltR6.lean`), so R′³/L₁′² says nothing about them. A census class keeps R and D = W − b fixed, and the far
shape holds on it only up to width 64D/15, so no class by itself holds a pass start that a halt from blank tape needs
(those are wider than 2⁴¹); what counts is whether a route's classes recur at every scale, as the lanes of A to C4 do.
All of these have R below 769, which the next section puts out of reach in Lean.

## The chain ends at a right end of at least 769

`LoopChain.small_end` (above, "No small right end past the loop") needs 178 only for the round-7 break. A run of full
passes from a loop entry is checked to end at no right end below 178 on each entry class (`smallOK`), and a round-7
break from a width of 2³⁷ lands with R′³/L₁′² ≥ (3E + 5R)/527,023 > 177³/9. From a width of 2⁴¹ the break lands higher.
It lands with 32R′ > S = 3E + 5R ≥ 3 · 2⁴¹ and 0 < 96L₁′ < 385 · 32R′, and to end at a right end r after p full passes
it needs R′ = 16^p · r and L₁′ = 64^p · ℓ with ℓ ≡ 3 (mod 7), so ℓ ≥ 3. For p ≤ 7 and r ≤ 768 that makes
32R′ ≤ 2³³ · 768 = 3 · 2⁴¹, too small; for p ≥ 8 it needs 96 · 4^p · ℓ < 12,320 · r, while the left side is at least
96 · 4⁸ · 3 = 18,874,368. So no run of full passes after a round-7 break from 2⁴¹ ends below 769 (`break7_noEnd769`,
`thm/BigEndHalt.lean`). R′³/L₁′² ≥ S/527,023 folds the two bounds into one and gives only 483; past 768 a break can end
after p = 7 full passes, but only from a width E < 2⁴¹ · r/768, and after p = 8 at r ≥ 1,533. The rest takes any bound
N: `NoEndBelow N`, `endOK N` and `bigEntryOK N` (`BB6/BigEnd.lean`) are `NoSmallAt`, `smallOK` and `smallEntryOK` with N
for 178, P past the linear bounds for right ends up to N − 1, and a width of at least 2⁴¹. A loop entry is far above
these right ends (R > W/29.02 at 36 digits, so R > 7.5 × 10¹⁰), so ending below 769 takes at least seven exact full
passes, R = 16^p · r and L₁ = 64^p · ℓ with p ≥ 7, and on a class of one coordinate R = 16^p · r fixes the point. Every
one of the 28,660 loop entries at 36 digits passes `bigEntryOK 769` (`cleanTreeGB`, `thm/CleanBigTheorem.lean`, has the
counts of `cleanTreeGS`, `thm/CleanBigMass.lean`), and an untrusted run of the same arithmetic finds no point of any
entry class that ends at a right end from 178 to 5,000, after a half pass or not (`../runs/chain_end.py`). So the
chain's last pass start has

    R ≥ 769 and 15W ≤ 64(W − b)      (`LoopChain.big_end`, `entry_big_halt`, `blank_halt_open_big`),

and what is left of the second question is the pass starts with both (`never_halts_of_big`). Every halting class with R
below 769 is out of reach, whatever its route, and with it every class of the census at R from 178 to 262, at 294 and at
486: the eight routes of the last section, the classes at R = 230 that close with no pass start after round 0, those
that land straight in the R = 2, 4 or 6 classes, and at R = 486 those on the lanes of routes C and C4 and the class with
W − b = 2,466 that lands at round 17 in the R = 4 class; and so are the families that the kernel proves halting and open
at every depth with R = 182 (`reentry6_open_halt`), R = 230 (`no_pass_open_halt`) and R = 486 (`lane486_open_halt`).

The class with W − b = 2,466 is the first of a lane that does not stop. The halting-classes census
(`routes/lanes_r294_486.json` and `routes/lanes_delta_eps.txt` in the project files) finds two lanes that close at every
right end tried with R ≡ 486 (mod 512) (δ) and R ≡ 486 (mod 1,024) (ε), from 486 to 4,582, and at every scale
Q + 636 = 2^j from the first with W − b ≥ R + 449 up to j = 30, with W − b = 2^j − 1,630 − 2(R − 486) and one class of b
at each R and j (for δ at R = 486, modulo 2¹⁶ at j = 12 and 2⁴⁴ at j = 30). Both re-enter the loop deep, with
W ≡ 2 (mod 4) at R′ = 2^(j−10) (δ, round 17) or 2^(j−8) (ε, round 13), and go on by a half pass and full passes to the
close, so R′³/L₁′² there is only about W/1.6 × 10¹² (δ) and W/2.3 × 10¹² (ε) at the edge of the far shape, too small to
exclude them below a width of about 2⁴⁷ (untrusted; their forms are observed on the model at three scales). The far
shape does not separate them either: full passes take W − b to about 15W/63 and L₁ = 35W − 147(W − b) + 392R − 186 near
0, which on these lanes is at W ≈ 4.2 · 2^j. Since they recur at right ends past every bound, no bound on R reaches
them.

Nor, by an untrusted count, does the chain from a loop entry of the 36-digit tree (`../runs/chain_lanes.py`). From an
entry class the chain makes a half pass first or not, then full passes and round-7 breaks, and each step's map divides
by a power of two; taking every step on the subclass where its divisions are exact gives a tree that holds every chain
from the class and more. Cut where a subclass's least member is wider than 2⁶³, it has 42,255 classes of one coordinate
from the 28,660 entries, none more than five steps from its entry (the blank-tape run to 2⁴² has no chain with more than
three landings, untrusted). On each class Q = W − b + 2R + 22 is affine with a large step, so a lane Q + c = 2^j holds
at one member at most for each j, and no member of any class meets a census lane at any j up to 64: not Q = 2^j or
3 · 2^j (routes A, C, β), Q + 36 = 2^j or 3 · 2^j (C3, C4, α), Q + 636 = 2^j (δ, ε), 3Q + 76 = 2^j (A3, C2) or
2Q − R + 6 = 2^j or 3 · 2^j (A2), nor those the census of R = 770 to 1,004 adds (`routes/lanes_r770_1004.txt`):
2Q − R + 26 = 2^j, Q + 316 = 2^j, Q + 636 = 3 · 2^j (δ's route to the right end 6), and, at the entries, which alone can
start a route with a half pass, Q + R + 24 and 2Q + R + 60 = 2^j or 3 · 2^j, Q + R + 96 and Q + R + 1,296 = 2^j, nor the
one the census at eight R from 5,002 to 5,862 adds, Q + 316 = 3 · 2^j (`routes/lanes_r5002_5862.txt`). Other small
offsets are met (the least are Q − 42 = 2^j and Q + 146 = 3 · 2^j), so this is a count, not a congruence. R′³/L₁′² rules
out δ and ε, and ε′ and ζ on the same lane (below), above a width of 2^52.7, or 2^61.1 against 177³/9, so if their forms
hold and the count is right, no chain from these entries reaches them.

That is not yet the run from blank tape. The loop entry of `blank_halt_open_big` is the first one in the cycle of a
clean tape, and it lies in one of these 28,660 classes only if `cleanTreeGB` settles that clean tape's class within 36
digits; in one of the 1,255,963 classes it cuts there, the entry is one that only a deeper tree finds. The 40-digit tree
has 169,631 entry classes (`EntryForms.lean` at 40 digits, 24 minutes), and the chains from them, 193,242 classes below
2⁶³, meet no census lane either; of all the offsets |c| ≤ 2,000 of the five forms scanned, the 140,971 new entries meet
one that the 36-digit ones do not (2Q + R − 1,538 = 3 · 2^j), a class found deeper having a larger step. In the
blank-tape run's sample of 1 in 16,384 cycles, of the 26,961 first entries after clean tapes wider than 2⁴¹, 11 lie in
none of the 36-digit classes and 3 in none of the 40-digit ones, all late in their cycle (rounds 43 to 52) and in cycles
that need 39 to 52 digits (`../runs/entry_member.py`, untrusted); the 430 later entries of a cycle lie in none, as they
come after the first entry's chain has ended and belong to the run from its last pass start. The cut classes keep their
number at every depth (next section), so no finite count covers every entry. Nor does every first entry pass the entry
check: the first entry in round 46 of n = 1,480,645,918,802 (a cycle that needs 47 digits, W ≈ 2^41.4) has
(W − b)/W = 0.1325, fails `EntryFar`, and is its chain's only pass start. The trees do not stop there: `RTree.exploreWE`
makes an entry leaf only where the check passes and otherwise follows the run on, here to the next clean tape, so the
theorems never take their pass start at such an entry (untrusted: the blank-tape run with every entry marked to width
2⁴³, where it is the only chain from a first entry without the far shape).

Most of the census routes need no count, though, and for those the entry does not matter (`../runs/lane_sigma.py`,
untrusted). On a route's lane R′ is fixed by the lane value and L₁′ is affine in the start, so over the pass starts of a
lane value with R ≥ 769, width at least 2⁴¹ and the far shape, which is what `blank_halt_open_big` leaves, the least
R′³/L₁′² is at a corner of a polygon, as for routes A to C4 above. Taken at the last three-wall start of every path of
the census at R = 770 to 1,004, of the census at eight R from 5,002 to 5,862, of δ and ε, and of ζ
(`routes/lanes_r770_1004_forms.txt`, `routes/lanes_r5002_5862_forms.txt`, `routes/lanes_r294_486.json` and
`routes/lanes_zeta_forms.txt`), with a path that begins with the loop's half pass taken at its landing, which is then
the chain's last pass start, the paths follow 18 routes (distinct pairs of forms R′, L₁′ there), and 8 of them are above
every bound their end can give at every lane value: r³/9 for each right end r of a halting class with R′ = 16^p · r, and
176³/256² for a close at the chain's end (`sigma_close`). These are the routes on Q, 3Q + 76, 2Q − R + 6, 2Q − R + 26
and Q + 36 = 2^j or 3 · 2^j, like A to C4. The ten left are on three lanes. On Q + 636 = 2^j or 3 · 2^j there are δ, up
to width 2^50.7 (lane values 2^j for j = 39 to 44, 47 and 48, and 3 · 2^j for j = 38 to 43 and 47); ε, up to 2^52.7 (2^j
for j = 39 to 46 and 50, 3 · 2^j for j = 38 to 43, 45 and 49; a path from R = 972 is ε at its landing, and the path at
R = 5,606 is ε); ε′, at R = 5,094 (R ≡ 998 mod 2,048 on its class), with ε's R′ and a larger L₁′, also up to 2^52.7 (2^j
for j = 39 to 46, 49 and 50, 3 · 2^j for j = 38 to 45 and 49); and ζ, at R ≡ 998 (mod 1,024; found at R = 998, 2,022 and
5,094), which re-enters in round 17 and makes its half pass in round 19 as δ does, with δ's R′ there and another L₁′, up
to 2^50.7 (2^j for j = 39 to 45, 47 and 48, 3 · 2^j for j = 38 to 43 and 47). On Q + 316 there are the route at R = 934
and two at R = 5,350 and 5,862 (R ≡ 230 mod 512), each only at 2⁴² and 3 · 2⁴¹, up to 2^44.7, and two at R = 5,350
(R ≡ 230 mod 1,024) that re-enter in round 11, up to 2^50.7 (2^j for j = 39 to 44 and 48, 3 · 2^j for j = 38 to 43 and
47). On Q + 36 there is a route that the half pass from R = 812 or 876 lands on, whose re-entry has L₁′ ≈ −35W, up to
2^51.7. Against 177³/9, which bounds every end below 178 (`noSmall_sigma`), every route is out above 2^61.1 (ε′; ε above
2^60.1). So the entries that only deeper trees find matter for these three lanes only, and only below 2^61.1, where the
count covers the 36- and 40-digit entries; and the halting-classes search finds no member of δ's lane Q + 636 = 2^j
wider than 2⁴¹ with the far shape at any R ≡ 486 (mod 512) up to j = 49, which with the ends' r³/9 covers δ's route on
that lane from every entry. Four paths have no three-wall start to take it at. Three stop at round 15 in the census
forms, before the round-17 start of δ or ζ: the class at R = 998 on Q + 636 = 3 · 2¹¹ (δ's route, which closes in the
R = 6 class), and two on Q + 636 = 2¹⁵, δ's at R = 5,094 and 5,606 and ζ's at R = 5,094. At R = 972 the class on
Q + R + 1,296 = 2¹³ makes only the half pass, onto Q + 636 = 2¹² at R = 486. A proof needs the routes' forms in Lean, an
argument for the three lanes from the entries of every depth, and on the halting side every halting class at every R,
not a census. There is no kernel-only version of `blank_halt_open_big`: its clean-tape tree starts at 2³⁷, where a
round-7 break clears only 383.

Above 769 the halting census finds the same lanes and three more (untrusted; `routes/lanes_r770_1004.txt` in the
project files). At every even R from 770 to 1,004 with W − b up to 4,096 it finds 236 closing classes, which fall on 91
paths when one point of each is followed with W − b and R left free. On each path the run reaches three-wall round
starts with right ends N/2^m for one linear form N, and halves down through them to the close; at every class N is
2^j or 3 · 2^j. The forms are those above, Q, 3Q + 76, 2Q − R + 6 and Q + 36, and three new ones,
2Q − R + 26 = 2^j (R ≡ 18 mod 64), Q + 316 = 2^j (R = 934) and Q + 636 = 3 · 2^j (δ at R = 998), each of which closes
again at larger scales. The other 25 paths begin with a half pass, from W ≡ 2 (mod 4) to R/2, so their starts are
never a chain's last pass start, and their conditions are these lanes at R/2. `lane769_open_halt`
(`thm/LaneHalt.lean`) proves a family with R ≥ 769 on each lane, and δ at R = 998 at each scale W − b = 2^j − 2,654
from j = 13 to 30, open at every depth and halting: the right end alone does not exclude a halting pass start.
`route769_open_halt` does the same for the routes this census misses: ζ at R = 998 at eleven scales from 2^14 to 2^22
(its first close there is at 2^14, above the census's W − b ≤ 4,096), and ε′, the four routes on Q + 316 at R ≡ 230 and
ε from the census at R = 5,002 to 5,862. Nor does the right end exclude it with the far shape: the member with walls 449, 2,462 and 15,193 and width 16,192 (δ at R = 998,
W − b = 2¹⁴ − 2,654) has 15W ≤ 64(W − b) (`lane769_far`). Only the width is missing: the pass start of
`blank_halt_open_big` is wider than 2⁴¹, and on δ at the scales from 2³⁹ to 2⁴⁹ no member at any R the lane allows
has both that width and b below 49(W − b)/15, as the far shape needs (untrusted: as R moves by 512, b's class moves by
1,024 · 7,394/7,247 as a 2-adic number at every scale from 2³¹ to 2⁴⁹, so over the lane b's classes lie on 7,247
progressions in R, and the least b/(W − b) at their starts doubles every two scales, 19.7 at 2³⁹ and 660 at 2⁴⁹).

## Deeper trees: the open classes keep their number

The clean tapes that both trees leave open are those in the cut classes of `cleanTreeGE 2⁴¹ d`. A deeper tree cuts
them finer, and the measure of what stays cut falls about 0.76-fold per digit (`thm/CleanEntryMass40.lean`,
`thm/CleanEntryMass44.lean`; `native_decide`, used by no theorem about the machine):

| depth | cut | clean | entries | cut measure | entries' measure |
|---|---|---|---|---|---|
| 36 | 1,255,963 | 1,163,068 | 28,660 | 1.83 × 10⁻⁵ | 1.34 × 10⁻³ |
| 40 | 6,582,732 | 6,106,591 | 169,631 | 5.99 × 10⁻⁶ | 1.34 × 10⁻³ |
| 44 | 33,928,389 | 32,073,443 | 734,274 | 1.93 × 10⁻⁶ | 1.34 × 10⁻³ |

These are evaluated on all cores: `BB6/MassPar.lean` cuts `exploreMassWE` at its 8th split level (`massPrefix`, and
`massPrefix_eq`: the tally is that of the leaves above the level plus those of the nodes on it, at most 2⁸) and
computes the nodes' tallies as tasks (`massPar`); logically `(Task.spawn f).get = f ()`, so `massPar_eq` follows from
`massPrefix_eq`, and native code runs the tasks in parallel (the 40-digit tree in 6 min 38 s on 4 cores instead of 22
minutes on one).

Their **number** at a fixed number of digits does not fall. Below almost every class cut at b digits, the tree of
depth b + r still has a cut leaf (`ProjPar.lean`, untrusted):

| cut at b digits | still cut below at b + r digits |
|---|---|
| 1,706 (b = 20) | 1,705 (r = 8) |
| 20,402 (b = 26) | 20,402 (r = 8) |
| 46,101 (b = 28) | 46,092 (r = 4) |
| 236,207 (b = 32) | 236,117 (r = 4) |
| 1,255,963 (b = 36) | 1,255,820 (r = 4) |

The open subtree below a cut class keeps branching (about 1.5-fold per digit) and almost never dies out. A
class that is cut at every depth holds a 2-adic value of W/2 whose run the tree never settles (the tree branches
finitely, so the cut classes below it have an infinite path), and the tree reads W/2 only as a 2-adic number on its
cone: an integer is set apart from the other 2-adic numbers only at the cone's edge, where a drop runs the smallest
member directly. So a 2-adic value that is not a width and never settles, such as the fixed point of a loop, keeps
every class it lies in open at every depth, and as measured nearly every cut class holds one: no depth of this tree
brings the number of cut classes at b digits down to zero, only their measure. Closing classes takes an argument that
uses that W is an integer, as the loop's lock does: after p full passes L₁ is 64^p·ℓ, and since L₁ ≡ 3 (mod 7) is never
0, an integer makes finitely many passes, while the 2-adic point at L₁ = 0 makes infinitely many.
A cut class holds not one of these values but a Cantor set of them (`../integ/INTEGRALITY.md`, October 27): below every
class cut at 24 digits but 2, the tree of depth 36 still cuts between 42 and 304 classes (`../integ/SpineCount.lean`,
`native_decide`), so a never-zero countdown for a class would vanish at infinitely many 2-adic points, and no lock of
the loop's kind can close one.

What the cut paths are made of (`CutShapes.lean`, untrusted, at 36 digits; the shapes at the cut agree with
`../lock/ShapeStats.lean`): 512,565 of the 1,255,963 (41%) stop at a two-marker state G 1, M m, M W − 2, and most others
a few rounds after one (127,863 two rounds after, 124,416 three); below the 8th split 85% of the paths pass 5 to 9
two-marker states. 133,177 (10.6%) end in a periodic stretch of round shapes (period at most 8, at least two periods):
the two-round loop G B → G W W (58,349) and loops through two-marker states, G M M → G M M M → G W M M (40,628), a
seven-round loop through G B and G W W (11,563) and G M M → G M W (7,279). The other 89% are aperiodic runs through
two-marker states, reading about one digit of W/2 per round, as the orbit of a Collatz-like map reads the digits of
its start. `../lock/LOCK_NOTES.md` (section 7) takes these runs apart into about 14,000 exact return pieces, from one
two-marker state to the next: each piece repeated alone is bounded by a never-zero countdown, like the loops above
(`../rec/twomarker_loops.py`), but no countdown is shared by the pieces, so none settles a class.

## What is trusted

`blank_halt_clean`, `blank_halt_structure` and `never_halts_of_cut_classes`: Lean's kernel, plus Lean's compiler
through `native_decide` for one evaluated check, `prefix_ok` (`#print axioms` lists it besides `propext`,
`Classical.choice` and `Quot.sound`). The clean-tape tree is not evaluated (the proved explorer), and the exit and
endgame trees are checked by the kernel itself (`decide +kernel`, subtree by subtree in `thm/ExitPieces*.lean` and
`thm/EndgamePieces*.lean`, assembled in `thm/ExitTheorem.lean` and `thm/EndgameTheorem.lean`). `blank_halt_clean_direct`
adds the direct runs (`clean_direct_ok`). `check_end.sh` compiles the BB6 modules to a shared library and loads it
with `--load-dynlib`, so that `native_decide` runs native code; this adds the C compiler to the trusted base
(`--interpreted` avoids it, at about an hour for the prefix alone).

`blank_halt_clean_entry`: as `blank_halt_clean_direct`; the tree with loop entries is not evaluated (the proved
explorer). `blank_halt_clean_entry_kernel`: Lean's kernel alone. `blank_halt_pass` and `blank_halt_pass_kernel`: the
same; the pass-start trees are not evaluated either (`PTree.explore_ok`). `blank_halt_open` and
`blank_halt_open_kernel`: the same as `blank_halt_pass` and `blank_halt_pass_kernel`. `blank_halt_small` and
`blank_halt_small_kernel`: the same; the small-end check is part of the explorer's entry test (`cleanSmallOK`), so
nothing is evaluated for it either. `blank_halt_open_small`, `blank_halt_open_small_kernel` and `never_halts_of_open`:
the same as `blank_halt_small` and `blank_halt_small_kernel`. `blank_halt_open_wide`, `never_halts_of_wide` and
`blank_halt_not_family`, and `blank_halt_open_wide_kernel`: the same as these; the wide check is part of the explorer's
entry test (`cleanWideOK`), and the shape follows from the steps' maps by `omega`. `blank_halt_open_far`,
`never_halts_of_far` and `blank_halt_open_far_kernel`: the same, with `cleanFarOK`. `blank_halt_open_big` and
`never_halts_of_big`: the same, with `cleanBigOK`.

`blank_halt_clean_kernel`, `blank_halt_structure_kernel` and `never_halts_of_cut_classes_kernel`: Lean's kernel
alone (`#print axioms` lists `propext`, `Classical.choice` and `Quot.sound`, nothing else). The prefix to 2³² cannot be
moved to kernel evaluation at any reasonable cost (1.2 × 10⁹ rounds; the kernel does about 600 rounds a second on
them), nor can the 26.5 million direct runs, but the run to 2²⁰ can: `blank_prefix_kernel` (`thm/PrefixKernel.lean`)
takes about 2 minutes on 4 cores, and the tree above it, like every clean-tape tree here, is not evaluated at all.

## What is not claimed

* **The clean tapes left open at every depth.** Nothing is said about them: whether the machine halts from one of them
  is exactly what remains open. At each depth they lie in the cut classes of that depth, the exhaustive check's open
  classes at 36 and 40 digits, whose measure falls about 0.76-fold per digit; that it falls to zero is a measurement,
  not a theorem (with the drops no class is cut at every depth because of the cone's edge, as the edge classes above
  were). Their number at a fixed number of digits does not fall with depth: nearly every cut class holds a 2-adic
  value of W/2 that no depth settles ("Deeper trees", above). In Lean such a clean tape is at least 2⁴¹ wide
  (`blank_halt_clean_direct`); combined with the exhaustive check (every clean tape below 2⁶¹ reaches the next one
  without halting; a C computation, not in Lean), at least 2⁶¹.
* **Item 3** is a statement about the stretches after a pass start, not a claim that a halt goes through the loop.
  The σ bound says that from a pass start beyond it a close through the loop needs a half pass or a round-7 break on
  the way (and from a width ≥ 2²⁴ a round-7 break is out); it does not bound σ itself. For the routes from
  two-marker states with both gaps at least Γ, the loop entries the route tree reaches are proved not to close at any
  width (`blank_halt_route`, `ROUTE_TREE.md`), and so are the clean-tape tree's (`blank_halt_clean_entry`); past the
  loop's end the pass-start trees follow the run to the next landing or a wider clean tape (`pass_halt_chain`, with
  their cut classes), and `blank_halt_pass` joins them to the clean-tape tree.
* **The pass starts that a pass-start tree cuts at every depth** (`pass_halt_chain`, `blank_halt_pass`). Nothing is said
  about them, and some of them halt: 1/8 of the pass starts with R = 6 close at distance 0 in round 7, and the machine
  halts there (`pass_r6_halt`). The run from blank tape reaches one only after a clean tape that the plain clean-tape
  tree leaves open at every depth (`blank_halt_open`), and none with R < 178 (`blank_halt_small`; both:
  `blank_halt_open_small`). Which of those with R ≥ 178 that `passTreeSym` cuts at every depth it can reach from there
  is not worked out; at the depths measured that tree's cuts are all depth cuts, none at a round decided as a halt, and
  they shrink with depth (8.8%, 3.8% and 1.6% of a class at 16, 20 and 24 splits). Some of them halt, at every width
  (`sym_open_halt`, `open_halt_families`, `reentry_open_halt`), also where a full pass of the loop's chain lands
  (`full_pass_open_halt`). The pass start a halt from blank tape needs has W ≤ 64R + 6 or 15W ≤ 64(W − b)
  (`blank_halt_open_wide`), so it is a member of none of these 29 families (`blank_halt_not_family`), and it has
  15W ≤ 64(W − b) (`blank_halt_open_far`), which keeps it off the eight routes of the halting classes with R = 178 to
  198 (untrusted), and R ≥ 769 (`blank_halt_open_big`), which keeps it out of every halting class with a smaller right
  end, whatever its route; whether the run reaches a pass start with R ≥ 769 and that shape that halts is open (two
  lanes of halting classes recur at every R ≡ 486, mod 512 or 1,024, from 998 on; an untrusted count of the pass starts
  to 2⁶³ of the chains from the loop entries of the 36- and 40-digit trees, `../runs/chain_lanes.py`, meets neither of
  them nor any other census lane, but deeper trees find more entries; R′³/L₁′² at the route's re-entry rules out every
  census route from any entry but ten, on Q + 636, Q + 316 and Q + 36, and those ten below width 2^61.1,
  `../runs/lane_sigma.py`). Pass starts with R ≥ 769 that halt, open at every depth, exist on every lane the census
  finds there (`lane769_open_halt`), and one meets every condition of `blank_halt_open_big` on the pass start but its
  width (`lane769_far`: width 16,192).
* The **two-marker route trees** (`ROUTE_TREE.md`) are not used by the theorems above: the machine's run reaches
  two-marker states with a small first gap again and again ("Why a one-variable tree", above). `blank_halt_route`
  (`thm/RouteEntryHalt.lean`) states what they give for a halting run from blank tape, at each two-marker state with
  both gaps at least Γ that it passes: unless the state is in a cut class of `routeTreeE Γ d` at every depth d, the
  run reaches the next clean tape or a loop entry from which the loop's chain ends without a close, and the halt comes
  after that.

## How to check

```sh
LEAN=/path/to/lean LEANLIB=/path/to/lib/lean ./check.sh       # the BB6 modules
LEAN=/path/to/lean LEANLIB=/path/to/lib/lean ./check_end.sh   # the theorem files, the direct runs, the 36-digit measures
LEAN=/path/to/lean LEANLIB=/path/to/lib/lean ./check_end.sh --deep   # also the 40-digit measures
LEAN=/path/to/lean LEANLIB=/path/to/lib/lean ./check_end.sh --deep --deeper  # and the 44-digit measure
# the tree's statistics, or the tree itself (optional, after check_end.sh; Γ = 2²⁰, 2³² or 2⁴¹):
LEAN_PATH=/path/to/lib/lean:out lean --load-dynlib=cbuild/so/libBB6all.so --run RouteStats.lean clean 4294967296 36 tree.txt
# the pass-start trees' leaves by kind and their halting leaves, d splits deep (optional, after check_end.sh; R < 178,
# sym for R ≥ 178, or all):
LEAN_PATH=/path/to/lib/lean:out lean --load-dynlib=cbuild/so/libBB6all.so --run PassStats.lean 16 6 64 sym
# the loop entries of the clean-tape tree with the small-end check, as forms in the class's coordinate (optional,
# after check_end.sh; Γ, d):
LEAN_PATH=/path/to/lib/lean:out lean --load-dynlib=cbuild/so/libBB6all.so --run EntryForms.lean 2199023255552 36
# and from those entries (saved to entries36.txt), whether a run of full passes ends at a right end from 178 to
# 5,000 (untrusted):
python3 ../runs/chain_end.py entries36.txt 178 5000
python3 ../runs/chain_lanes.py entries36.txt 63 2000
# the same from the entries at 40 digits (EntryForms.lean 2199023255552 40, saved to entries40.txt), and which of the
# blank-tape run's sampled loop entries lie in the classes (untrusted):
python3 ../runs/chain_lanes.py entries40.txt 63 2000
python3 ../runs/entry_member.py ../blankrun/results/sample16k.tsv.gz entries36.txt entries40.txt
# which census lanes R'^3/L1'^2 at the route's re-entry rules out at the chain's last pass start, from any entry (the
# forms from routes/ in the halting-classes project files; untrusted):
python3 ../runs/lane_sigma.py lanes_r770_1004_forms.txt lanes_r5002_5862_forms.txt lanes_r294_486.json lanes_zeta_forms.txt
# the loop entries followed in the clean tape's coordinate (optional, after check_end.sh; Γ, d, e splits, landings):
LEAN_PATH=/path/to/lib/lean:out lean --load-dynlib=cbuild/so/libBB6all.so --run ReachStats.lean 2199023255552 28 12 4
# whether deeper trees close the cut classes at b digits (optional, after check_end.sh; b, r more splits, Γ):
LEAN_PATH=/path/to/lib/lean:out lean --load-dynlib=cbuild/so/libBB6all.so --run ProjPar.lean 36 4 2199023255552
# the round shapes on the cut paths, with their periodic tails (optional, after check_end.sh; Γ, d):
LEAN_PATH=/path/to/lib/lean:out lean --load-dynlib=cbuild/so/libBB6all.so --run CutShapes.lean 2199023255552 36
# the class of pass starts with R ≥ 178 that halts at a scale j, a family's checks, a run's rounds (optional, after
# check_end.sh; search pow j rlo rhi K S, fam W₀ R₀ b₀ k, trace n a b W R):
LEAN_PATH=/path/to/lib/lean:out lean --load-dynlib=cbuild/so/libBB6all.so --run HaltClasses.lean search pow 12 178 198 24 54
# the checkpoints of the run to 2²⁰ and the kernel-checked prefix from them (optional; the files are in the repository):
LEAN_PATH=/path/to/lib/lean:out lean --run PrefixGen.lean 1048576 5000 checkpoints.txt
python3 thm/gen_prefix.py checkpoints.txt thm 8
```

## Running time (Lean 4.34.0 release build, native code via `--load-dynlib`, 4 cores)

| step | time |
|---|---|
| `thm/PrefixPieces*.lean`, `thm/ExitPieces*.lean`, `thm/EndgamePieces*.lean` (kernel, 4 modules at a time; the prefix pieces take about 2 min of it) | 3 min 49 s |
| `thm/PrefixKernel.lean`, `EndgameTheorem.lean`, `ExitTheorem.lean`, `ExitHalt.lean`, `LoopTheorem.lean`, `LoopHalt.lean`, `PassHalt.lean`, `PassHaltR6.lean`, `PassHaltClasses.lean` | seconds |
| `thm/PassOpenHalt.lean` (the families' model runs by the kernel) | 2 min 19 s beside the other theorem files |
| `thm/LaneHalt.lean` (57 families, by the kernel) | about 1 to 2 min |
| `thm/Prefix.lean` (1.2 × 10⁹ rounds) | 4 min 20 s |
| `thm/CleanTheorem.lean`, `thm/EndToEnd.lean`, `thm/EndToEndDirect.lean`, `thm/RouteTheorem.lean`, `thm/RouteEntryTheorem.lean`, `thm/RouteEntryHalt.lean`, `thm/CleanEntryTheorem.lean`, `thm/CleanEntryHalt.lean`, `thm/PassEntryHalt.lean`, `thm/CleanSmallTheorem.lean`, `thm/SmallEndHalt.lean`, `thm/OpenSmallHalt.lean`, `thm/CleanWideTheorem.lean`, `thm/WideHalt.lean`, `thm/CleanFarTheorem.lean`, `thm/FarHalt.lean`, `thm/CleanBigTheorem.lean`, `thm/BigEndHalt.lean` | seconds |
| `thm/CleanEntryMass.lean` (36 digits, cone 2⁴¹, with loop entries) | 5 min 1 s |
| `thm/CleanSmallMass.lean` (36 digits, cone 2⁴¹, with loop entries and the small-end check) | about 5 min 30 s (2 min 26 s on a machine where `CleanEntryMass` takes 2 min 11 s) |
| `thm/CleanWideMass.lean` (36 digits, cone 2⁴¹, with loop entries, the small-end check and W ≤ 32R) | 3 min 41 s alone |
| `thm/CleanFarMass.lean` (the same with 15W ≤ 64(W − b) and 15W + 26 ≤ 32(W − b + R) for W ≤ 32R) | 3 min 39 s beside the other mass files |
| `thm/CleanBigMass.lean` (36 digits, cone 2⁴¹, with loop entries, the far test and no end below 769) | 5 min 36 s beside the other mass files |
| `thm/CleanEntryKernelMass.lean` (36 digits, cone 2²⁴, with loop entries) | 5 min 6 s |
| `thm/CleanMass.lean` (36 digits, 3.2 million leaves) | 4 min 46 s |
| `thm/CleanKernelMass.lean` (36 digits, cone 2²⁰) | 5 min 27 s |
| `thm/CleanDirect.lean` (the 36-digit tree, then 26,508,327 direct runs) | 13 min 22 s |
| `thm/CleanDirectMass.lean` (36 digits, cone 2⁴¹) | 5 min 29 s |
| `thm/CleanMass40.lean`, `thm/CleanDirectMass40.lean` (40 digits, `--deep`) | 30 min each |
| `thm/CleanEntryMass40.lean` (40 digits, cone 2⁴¹, with loop entries, `massPar` on 4 cores, `--deep`) | 6 min 38 s alone (24 min of CPU), 14 min 54 s beside the other `--deep` files |
| `thm/CleanEntryMass44.lean` (44 digits, the same, `--deeper`) | 58 min 51 s beside the `--deep` files (2 h 2 min of CPU) |

The whole of `check_end.sh --deep` took 38 min 51 s (4 cores; the files of a stage run in parallel, and the two 40-digit
measures, side by side, set the time); without `--deep` it took 24 min 22 s when last measured (October 28).
`check_end.sh --deep --deeper` took 71 min 19 s, the 44-digit measure setting the time.
