import EndToEnd
import LoopClose
open BB6 BB6.Sym

/-!
# End to end, with end meetings at distance 2 passed

`blank_halt_structure` (`thm/EndToEnd.lean`) with its item 3 from `loop_chain_halt_close` (`thm/LoopClose.lean`):
after the loop's chain from each pass start it passes with every gap at least 448, a halt from blank tape needs a
stuck configuration right at the chain's last pass start, with R₁ in {2, 4, 8, 16, 32, 48} and the left countdown in
R₁'s class of `closeClassC` (`InCloseClassC`), or after a further stretch, with every end meeting at distance at least
2, to where the run leaves the chain (`LoopEnd`).  `blank_halt_sigma_close` and `blank_halt_wide_close` are
`blank_halt_sigma` and `blank_halt_wide` with these classes: the σ bound is R³/L₁² ≤ 4 (log₂W ≤ σ + 2), and from a
width of 2²⁰, the width of the kernel's prefix, a close through the loop makes no round-7 break.
`blank_halt_structure_close_kernel` is `blank_halt_structure_kernel` with item 3 so; nothing in it is evaluated by
compiled code. -/

namespace BB6

/-- **What a halt from blank tape needs after a pass start, with end meetings at distance 2 passed.**
`blank_halt_loop` with `loop_chain_halt_close`: from every phase-0 pass start the machine passes on its way with every
gap at least 448, the run follows the loop's chain (`LoopChain`) to its last pass start (right end R₁), and the halt
needs a stuck configuration after it: either right there, with R₁ in {2, 4, 8, 16, 32, 48} and the left countdown in
R₁'s class of `closeClassC` (`InCloseClassC`), or after a further stretch, with every end meeting at distance at
least 2, to where the run leaves the chain (`LoopEnd`). -/
theorem blank_halt_loop_close (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∀ (R : Nat) (ms : List Mark) (W k : Nat), PassStart448 ms W R →
      steps k ⟨blank, blank, .A⟩ = some (roundStart ms W) →
      ∃ ks ms₁ W₁ R₁, LoopChain ms W R ks ms₁ W₁ R₁ ∧
        ((InCloseClassC ms₁ W₁ R₁ ∧ ∃ t, Reach ⟨[], 1, ms₁, W₁⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
          ∃ n ms' W', roundsZ 1000 n ms₁ W₁ = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n ms₁ W₁, 2 ≤ d) ∧
            LoopEnd W₁ R₁ (passL1 ms₁ W₁) n (meetsRounds 1000 n ms₁ W₁) ms' W' ∧
            ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) := by
  intro R ms W k hP hk
  obtain ⟨-, hT'⟩ := steps_none_split hT hk
  exact loop_chain_halt_close _ R ms W hP hT'

/-- **The σ bound from blank tape, with end meetings at distance 2 passed.**  `blank_halt_sigma` with
`loop_halt_sigma_close`: at no phase-0 pass start the machine passes on its way with every gap at least 448 and
R³/L₁² > 4 (log₂W > σ + 2) does it close through full passes alone: the loop's chain from there either makes a half
pass or a round-7 break before it reaches a class of `closeClassC`, or it ends (`LoopEnd`) and the halt needs a stuck
configuration after that. -/
theorem blank_halt_sigma_close (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∀ (R : Nat) (ms : List Mark) (W k : Nat), PassStart448 ms W R → ¬ SigmaOKC R (passL1 ms W) →
      steps k ⟨blank, blank, .A⟩ = some (roundStart ms W) →
      ∃ ks ms₁ W₁ R₁, LoopChain ms W R ks ms₁ W₁ R₁ ∧
        ((InCloseClassC ms₁ W₁ R₁ ∧ (StepKind.half ∈ ks ∨ StepKind.break7 ∈ ks) ∧
            ∃ t, Reach ⟨[], 1, ms₁, W₁⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
          ∃ n ms' W', roundsZ 1000 n ms₁ W₁ = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n ms₁ W₁, 2 ≤ d) ∧
            LoopEnd W₁ R₁ (passL1 ms₁ W₁) n (meetsRounds 1000 n ms₁ W₁) ms' W' ∧
            ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) := by
  intro R ms W k hP hσ hk
  obtain ⟨-, hT'⟩ := steps_none_split hT hk
  exact loop_halt_sigma_close R ms W hP hσ _ hT'

/-- **Wide pass starts from blank tape, with end meetings at distance 2 passed.**  `blank_halt_wide` with
`loop_halt_wide_close`, from a width of 2²⁰ instead of 2²⁴: from every phase-0 pass start the machine passes on its way
with width W ≥ 2²⁰ and every gap at least 448, the loop's chain either reaches a class of `closeClassC` without a
round-7 break, through p full passes or a half pass from W ≡ 2 (mod 4) and then p full passes, and the halt needs a
stuck configuration after it; or it ends (`LoopEnd`) and the halt needs a stuck configuration after that. -/
theorem blank_halt_wide_close (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∀ (R : Nat) (ms : List Mark) (W k : Nat), PassStart448 ms W R → 2 ^ 20 ≤ W →
      steps k ⟨blank, blank, .A⟩ = some (roundStart ms W) →
      ∃ ks ms₁ W₁ R₁, LoopChain ms W R ks ms₁ W₁ R₁ ∧
        ((InCloseClassC ms₁ W₁ R₁ ∧
            (∃ p, (ks = List.replicate p .full ∧ R = 16 ^ p * R₁ ∧ passL1 ms W = 64 ^ p * passL1 ms₁ W₁) ∨
              (ks = .half :: List.replicate p .full ∧ W % 4 = 2 ∧ R = 2 * 16 ^ p * R₁ ∧
                2 * 64 ^ p * passL1 ms₁ W₁ = passL1 ms W + 35 * (W : Int) - 147 * (R : Int) - 60)) ∧
            ∃ t, Reach ⟨[], 1, ms₁, W₁⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
          ∃ n ms' W', roundsZ 1000 n ms₁ W₁ = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n ms₁ W₁, 2 ≤ d) ∧
            LoopEnd W₁ R₁ (passL1 ms₁ W₁) n (meetsRounds 1000 n ms₁ W₁) ms' W' ∧
            ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) := by
  intro R ms W k hP hW hk
  obtain ⟨-, hT'⟩ := steps_none_split hT hk
  exact loop_halt_wide_close R ms W hP hW _ hT'

/-- **End to end, with end meetings at distance 2 passed.**  `blank_halt_structure` with item 3 from
`blank_halt_loop_close`: if the machine, started on blank tape, halts after T steps, then (1) it first reaches a clean
tape of even width W ≥ 2³² with W/2 in a cut class of the clean-tape tree at every depth, halts from it, and the mark
model, run from it, reaches a stuck configuration; (3) after the loop's chain from every pass start it passes with
every gap at least 448, the halt needs a stuck configuration right at the chain's last pass start, with R₁ in
{2, 4, 8, 16, 32, 48} and the left countdown in R₁'s class of `closeClassC`, or after a further stretch, with every
end meeting at distance at least 2, to where the run leaves the chain (`LoopEnd`); (4) every loop state it passes is
followed by the certified exit stretch, and the halt needs a stuck configuration after it. -/
theorem blank_halt_structure_close (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    (∃ W k, prefixWidth ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTree d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∧
    (∀ (R : Nat) (ms : List Mark) (W k : Nat), PassStart448 ms W R →
      steps k ⟨blank, blank, .A⟩ = some (roundStart ms W) →
      ∃ ks ms₁ W₁ R₁, LoopChain ms W R ks ms₁ W₁ R₁ ∧
        ((InCloseClassC ms₁ W₁ R₁ ∧ ∃ t, Reach ⟨[], 1, ms₁, W₁⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
          ∃ n ms' W', roundsZ 1000 n ms₁ W₁ = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n ms₁ W₁, 2 ≤ d) ∧
            LoopEnd W₁ R₁ (passL1 ms₁ W₁) n (meetsRounds 1000 n ms₁ W₁) ms' W' ∧
            ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t))) ∧
    (∀ (a b c E k : Nat), a % 2 = 1 → b % 2 = 0 → c % 2 = 1 → E % 2 = 0 →
      390 ≤ a → a + 390 ≤ b → b + 390 ≤ c → c + 390 ≤ E →
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E) →
      ∃ n ms' W', roundsZ 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E = .newRound ms' W' ∧
        (∀ d ∈ meetsRounds 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E, 3 ≤ d) ∧
        ExitEvent n (meetsRounds 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E) ms' W' ∧
        ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) :=
  ⟨blank_halt_clean T hT, blank_halt_loop_close T hT, blank_halt_exit T hT⟩

/-- **End to end, checked by the kernel alone, with end meetings at distance 2 passed.**
`blank_halt_structure_close` with item 1 from the kernel's prefix (`blank_halt_clean_kernel`): the clean tape a halt
needs is at least 2²⁰ wide, and W/2 lies in a cut class of the clean-tape tree over the widths ≥ 2²⁰ at every depth.
Nothing here is evaluated by compiled code. -/
theorem blank_halt_structure_close_kernel (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    (∃ W k, kernelPrefixWidth ≤ W ∧ W % 2 = 0 ∧
      (∀ d, (cleanTreeG kernelPrefixWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∧
    (∀ (R : Nat) (ms : List Mark) (W k : Nat), PassStart448 ms W R →
      steps k ⟨blank, blank, .A⟩ = some (roundStart ms W) →
      ∃ ks ms₁ W₁ R₁, LoopChain ms W R ks ms₁ W₁ R₁ ∧
        ((InCloseClassC ms₁ W₁ R₁ ∧ ∃ t, Reach ⟨[], 1, ms₁, W₁⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
          ∃ n ms' W', roundsZ 1000 n ms₁ W₁ = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n ms₁ W₁, 2 ≤ d) ∧
            LoopEnd W₁ R₁ (passL1 ms₁ W₁) n (meetsRounds 1000 n ms₁ W₁) ms' W' ∧
            ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t))) ∧
    (∀ (a b c E k : Nat), a % 2 = 1 → b % 2 = 0 → c % 2 = 1 → E % 2 = 0 →
      390 ≤ a → a + 390 ≤ b → b + 390 ≤ c → c + 390 ≤ E →
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E) →
      ∃ n ms' W', roundsZ 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E = .newRound ms' W' ∧
        (∀ d ∈ meetsRounds 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E, 3 ≤ d) ∧
        ExitEvent n (meetsRounds 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E) ms' W' ∧
        ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) :=
  ⟨blank_halt_clean_kernel T hT, blank_halt_loop_close T hT, blank_halt_exit T hT⟩

#print axioms blank_halt_loop_close
#print axioms blank_halt_sigma_close
#print axioms blank_halt_wide_close
#print axioms blank_halt_structure_close
#print axioms blank_halt_structure_close_kernel

end BB6
