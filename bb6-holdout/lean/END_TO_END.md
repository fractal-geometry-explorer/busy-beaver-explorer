# End to end: what a halt from blank tape needs

`thm/EndToEnd.lean` puts the Lean results together into one statement about the machine
`1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE` started on blank tape. It does not settle the question. It says exactly
where a halt would have to come from: a clean tape of width at least 2³² that the clean-tape tree leaves open at
**every** depth. The classes it leaves open are exactly the exhaustive check's open classes: at 36 digits 1,660,024 of
measure 2.4 × 10⁻⁵, at 40 digits 9,188,898 of measure 8.4 × 10⁻⁶. With the clean tapes below 2⁴¹ in those classes run
one by one (`thm/EndToEndDirect.lean`, 26,508,327 runs), the clean tape a halt needs is at least 2⁴¹ wide. The same
statement from width 2²⁰ (`blank_halt_structure_kernel`) is checked by Lean's kernel alone, with no `native_decide`;
the tree it uses, over the widths ≥ 2²⁰, leaves the same classes open. With the loop entries
(`thm/CleanEntryHalt.lean`, below), the clean-tape tree also stops at the pass starts from which no member of the
class can close through the loop, and a halt needs a clean tape in its cut classes at every depth (at 36 digits
1,255,963 classes, measure 1.83 × 10⁻⁵, over the widths ≥ 2⁴¹), or such a loop entry, from which the loop's chain ends
without a close where the run leaves three walls. The pass-start trees (`thm/PassHalt.lean`) follow the run on from
there, and the two join (`thm/PassEntryHalt.lean`, `blank_halt_pass`): a halt from blank tape needs a clean tape of
width ≥ 2⁴¹ in a cut class of the clean-tape tree with loop entries at every depth, or a pass start wider than 2⁴¹ in
a cut class of its pass-start tree at every depth. Some pass starts in those classes do halt, so the question is now
whether the run from blank tape reaches one of them, or one of those clean tapes.

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

An end meeting at distance 2 is not a halt. In every closing class with R ≥ 4 the endgame trees' close is an end
meeting at distance 2, after which the round model goes on to a new round start; the pass-start trees run on through
such rounds, and only a landing reached that way is not a step of the chain (the tree runs past it, to a clean tape).
A round that the model decides otherwise (a halt, or a close at distance 0, which the model leaves uncovered) ends a
path: at a close leaf when L₁ is in R's closing class, at a cut otherwise. These are real halts. 1/8 of the pass
starts with R = 6, which is outside the closing set, leave phase 0 at round 2, meet the end at distance 2 in round 5
and at distance 0 in round 7, at every width; from walls 743, 1,802, 3,319 and width 3,326 the machine halts after
11,362,209 steps, and all 49 such starts among 400 random ones of width below 8,400 halt when the machine is run (two
simulators, from `roundStart` as defined in `BB6/Marks.lean`). Of 40 random pass starts of width below 4,300 for each
R, 14 halt with R = 4, 3 with R = 6, 7 with R = 8, none with R = 10, 22 or 64. So the cut classes of the pass-start trees
do not shrink to nothing; what `pass_halt_chain` says is that a halt through a pass start needs one of them, or a
closing class, or a clean tape after it.

The cut leaves' measure (`PassStats.lean`; fractions of a start class): at 16 splits 4.8% on average over the trees for
R < 178 (4.2% where the depth ran out, 0.5% where a round is undecided and its undecided residue is not found, 0.1% at a
decided halt, R = 6's 1/8), and 8.8% for R ≥ 178; at 20 splits 2.4% (1.6%, 0.7% and 0.1%) and 4.1%. Landings take 12% of
a class, clean tapes 81%, close leaves 1.6%.

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
| `BB6/PassTree.lean`, `thm/PassHalt.lean` | `PTree.sound`: a pass-start tree's check gives, at every point of its class, a cut leaf, the left countdown in the closing class, or a halt-free run to a close-free landing of the chain or a wider clean tape; `PTree.explore_ok`: every tree the explorer builds passes the check; `pass_next`: from every pass start with gaps ≥ 448, at every depth; `pass_halt_chain`: a halt from a pass start of width ≥ 2¹³ follows the chain to a last pass start in a closing class, or cut at every depth, or goes on to a wider clean tape | the proved explorer, nothing evaluated; induction on the halting time through `landing_wide` and `halt_after_rounds` |
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
| `thm/PassEntryHalt.lean` | `LoopChain.reach`: the loop's chain is a run of the machine; `entry_pass_halt`: a halt from a loop entry that cannot close needs the loop's chain to a last pass start in a cut leaf of its pass-start tree at every depth, or a wider clean tape that the run reaches and halts from; `blank_halt_pass_from`, `blank_halt_pass`, `blank_halt_pass_kernel`: from blank tape, a clean tape cut at every depth or such a pass start | `pass_halt_chain` with `EntryNoClose.no_close`, as `clean_entry_chain`'s hypothesis on the entries; nothing evaluated |
| `thm/CleanEntryMass.lean`, `thm/CleanEntryKernelMass.lean` | `clean_tree_entry_cut_mass`, `clean_entry_kernel_cut_mass`: the leaf counts and measures of `cleanTreeGE 2⁴¹ 36` and `cleanTreeGE 2²⁴ 36` | `exploreMassWE`, `native_decide`; used by no theorem about the machine |

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
measure 1.83 × 10⁻⁵ at 36 digits, and their number grows about 1.52-fold per digit, so their measure shrinks with
depth. The pass-start trees' are 2.4% of a start class at 20 splits for R < 178 and 4.1% for R ≥ 178, and they do not
shrink to nothing, since some of them are real halts (1/8 of the pass starts with R = 6, above). So no depth of the
pass-start trees can show that their cut classes do not halt. What `blank_halt_pass` leaves open is whether the run
from blank tape reaches one of the pass starts that halt, or a clean tape of the cut classes. The pass starts it can
reach that way are the last pass starts of loop chains from the clean-tape tree's entries; following the entries'
classes through the chain and into the pass-start trees would say which of the pass-start trees' cut classes those
are.

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
same; the pass-start trees are not evaluated either (`PTree.explore_ok`).

`blank_halt_clean_kernel`, `blank_halt_structure_kernel` and `never_halts_of_cut_classes_kernel`: Lean's kernel
alone (`#print axioms` lists `propext`, `Classical.choice` and `Quot.sound`, nothing else). The prefix to 2³² cannot be
moved to kernel evaluation at any reasonable cost (1.2 × 10⁹ rounds; the kernel does about 600 rounds a second on
them), nor can the 26.5 million direct runs, but the run to 2²⁰ can: `blank_prefix_kernel` (`thm/PrefixKernel.lean`)
takes about 2 minutes on 4 cores, and the tree above it, like every clean-tape tree here, is not evaluated at all.

## What is not claimed

* **The clean tapes left open at every depth.** Nothing is said about them: whether the machine halts from one of them
  is exactly what remains open. At each depth they lie in the cut classes of that depth, the exhaustive check's open
  classes at 36 and 40 digits, whose measure falls about 0.76-fold per digit; that it falls to zero is a measurement,
  not a theorem (with the drops no class is cut at every depth for a reason of method, as the edge classes above
  were). In Lean such a clean tape is at least 2⁴¹ wide
  (`blank_halt_clean_direct`); combined with the exhaustive check (every clean tape below 2⁶¹ reaches the next one
  without halting; a C computation, not in Lean), at least 2⁶¹.
* **Item 3** is a statement about the stretches after a pass start, not a claim that a halt goes through the loop.
  The σ bound says that from a pass start beyond it a close through the loop needs a half pass or a round-7 break on
  the way (and from a width ≥ 2²⁴ a round-7 break is out); it does not bound σ itself. For the routes from
  two-marker states with both gaps at least Γ, the loop entries the route tree reaches are proved not to close at any
  width (`blank_halt_route`, `ROUTE_TREE.md`), and so are the clean-tape tree's (`blank_halt_clean_entry`); past the
  loop's end the pass-start trees follow the run to the next landing or a wider clean tape (`pass_halt_chain`, with
  their cut classes), and `blank_halt_pass` joins them to the clean-tape tree.
* **The pass starts that a pass-start tree cuts at every depth** (`pass_halt_chain`, `blank_halt_pass`). Nothing is
  said about them, and some of them halt: 1/8 of the pass starts with R = 6 close at distance 0 in round 7, and the
  machine halts there. Which of them the run from blank tape can reach is not worked out.
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
# the tree's statistics, or the tree itself (optional, after check_end.sh; Γ = 2²⁰, 2³² or 2⁴¹):
LEAN_PATH=/path/to/lib/lean:out lean --load-dynlib=cbuild/so/libBB6all.so --run RouteStats.lean clean 4294967296 36 tree.txt
# the pass-start trees' leaves by kind, d splits deep (optional, after check_end.sh; R < 178, sym for R ≥ 178, or all):
LEAN_PATH=/path/to/lib/lean:out lean --load-dynlib=cbuild/so/libBB6all.so --run PassStats.lean 16 6 64 sym
# the checkpoints of the run to 2²⁰ and the kernel-checked prefix from them (optional; the files are in the repository):
LEAN_PATH=/path/to/lib/lean:out lean --run PrefixGen.lean 1048576 5000 checkpoints.txt
python3 thm/gen_prefix.py checkpoints.txt thm 8
```

## Running time (Lean 4.34.0 release build, native code via `--load-dynlib`, 4 cores)

| step | time |
|---|---|
| `thm/PrefixPieces*.lean`, `thm/ExitPieces*.lean`, `thm/EndgamePieces*.lean` (kernel, 4 modules at a time; the prefix pieces take about 2 min of it) | 3 min 49 s |
| `thm/PrefixKernel.lean`, `EndgameTheorem.lean`, `ExitTheorem.lean`, `ExitHalt.lean`, `LoopTheorem.lean`, `LoopHalt.lean`, `PassHalt.lean` | seconds |
| `thm/Prefix.lean` (1.2 × 10⁹ rounds) | 4 min 20 s |
| `thm/CleanTheorem.lean`, `thm/EndToEnd.lean`, `thm/EndToEndDirect.lean`, `thm/RouteTheorem.lean`, `thm/RouteEntryTheorem.lean`, `thm/RouteEntryHalt.lean`, `thm/CleanEntryTheorem.lean`, `thm/CleanEntryHalt.lean`, `thm/PassEntryHalt.lean` | seconds |
| `thm/CleanEntryMass.lean` (36 digits, cone 2⁴¹, with loop entries) | 5 min 1 s |
| `thm/CleanEntryKernelMass.lean` (36 digits, cone 2²⁴, with loop entries) | 5 min 6 s |
| `thm/CleanMass.lean` (36 digits, 3.2 million leaves) | 4 min 46 s |
| `thm/CleanKernelMass.lean` (36 digits, cone 2²⁰) | 5 min 27 s |
| `thm/CleanDirect.lean` (the 36-digit tree, then 26,508,327 direct runs) | 13 min 22 s |
| `thm/CleanDirectMass.lean` (36 digits, cone 2⁴¹) | 5 min 29 s |
| `thm/CleanMass40.lean`, `thm/CleanDirectMass40.lean` (40 digits, `--deep`) | 30 min each |

The whole of `check_end.sh --deep` took 38 min 51 s (4 cores; the files of a stage run in parallel, and the two
40-digit measures, side by side, set the time); without `--deep` it took 21 min 37 s when last measured, before the
drop nodes.
