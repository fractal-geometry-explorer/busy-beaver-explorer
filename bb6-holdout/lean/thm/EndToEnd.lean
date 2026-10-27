import Prefix
import PrefixKernel
import CleanTheorem
import LoopHalt
import ExitHalt

/-!
# End to end: what a halt of the machine from blank tape needs

The pieces, all theorems about the machine `1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE` started on blank tape:

* `blank_prefix` (`thm/Prefix.lean`): the machine reaches the one-marker clean tape of width 2³² without halting
  (1.2 × 10⁹ rounds, evaluated by `native_decide`).  `blank_prefix_kernel` (`thm/PrefixKernel.lean`): the same to the
  clean tape of width 2²⁰, checked by Lean's kernel.
* `clean_tree_step_G` (`thm/CleanTheorem.lean`): for every Γ ≥ 6 and every depth d, from every clean tape of width
  W ≥ Γ, the machine reaches a wider clean tape without halting, unless W/2 lies in one of the cut classes of the
  depth-d clean-tape tree over the widths ≥ Γ (`cleanTreeG Γ d`, built by the proved explorer of
  `BB6/RouteExplore.lean`, so nothing is evaluated); `cleanTree d` is the tree over the widths ≥ 2³².
* `round_halt_needs_contact`, `stuck_cases` (`BB6/HaltClose`, `BB6/HaltStretch`): a halt from a round start needs
  the mark model, run from there, to reach a stuck configuration: a close at the right end or an interior contact.
* `loop_chain_halt` (`thm/LoopHalt.lean`): a halt from a phase-0 pass start with every gap at least 448 comes only
  after the loop's chain from it (`LoopChain`: full passes, round-7 breaks and a half pass, only as the first step,
  each close-free with its exact map on the width, the right end and the left countdown L₁, each to a pass start with
  gaps again all ≥ 448), and needs a stuck configuration after it: at the chain's last pass start, with R in the
  closing set and L₁ in R's class, or after the run leaves the chain (`LoopEnd`).  `loop_halt_sigma` is the σ bound:
  from a pass start with R³/L₁² > 176³/256² (log₂W > σ + 6.38), a close through the loop needs a half pass or a
  round-7 break on the way.  `loop_halt_wide`: from a pass start of width at least 2²⁷, a close through the loop
  makes no round-7 break.
* `exit_halt_needs_contact` (`thm/ExitHalt.lean`): a halt from a loop state comes only after its certified exit
  stretch, which ends at a clean tape, a break of the end-meeting chain or a loop state again (`ExitEvent`), and needs
  a stuck configuration after it.

`clean_chain` chains the clean-tape steps by strong induction on the halting time (a run from a clean tape to a wider
one takes at least one step, `roundStart_one_ne`): at each clean tape, either it is in the cut classes at every depth,
or some depth decides it and the run goes on to a wider clean tape.  `blank_halt_clean_from` adds a prefix and the
stuck configuration, for any bounds A ≤ B below which every clean tape of width ≥ A reaches a wider one
(`StepsBelow A B`): `blank_halt_clean` uses it with the prefix to 2³² and A = B = 2³², `blank_halt_clean_kernel` with
the kernel's prefix to 2²⁰ and A = B = 2²⁰, and `thm/EndToEndDirect.lean` with the prefix to 2³², A = 2³² and
B = 2⁴¹.  `blank_halt_loop` adds the pass starts (`blank_halt_sigma` the σ bound, `blank_halt_wide` the pass starts
of width at least 2²⁷), `blank_halt_exit` the loop states,
and `blank_halt_structure` is the three together; `blank_halt_structure_kernel` is the same with
`blank_halt_clean_kernel`, and its axioms are Lean's standard three alone: no evaluation by compiled code is trusted.

**What is not claimed.**  Nothing is said about the clean tapes that are in the cut classes at every depth: whether
the machine halts from one of them is exactly what remains open.  At each depth d the cut classes are residue classes
of W/2 modulo powers of two up to 2^d; their measure is evaluated in `thm/CleanMass.lean` (2.4 × 10⁻⁵ at 36 digits
over the widths ≥ 2³²) and `thm/CleanKernelMass.lean` (2.9 × 10⁻⁵ over the widths ≥ 2²⁰), and the clean tape a halt
needs lies in all of them.
-/

namespace BB6
open BB6.Sym

theorem noG_one (W : Nat) : noG [⟨.M, W⟩] := by
  intro m hm
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
  subst hm; simp

/-- Every clean tape of even width in [A, B) reaches a wider one-marker clean tape. -/
def StepsBelow (A B : Nat) : Prop :=
  ∀ W, W % 2 = 0 → A ≤ W → W < B →
    ∃ n k W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound [⟨.M, W' - 2⟩] W' ∧
      steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.M, W' - 2⟩] W') ∧ 0 < n ∧ W < W'

theorem stepsBelow_self (A : Nat) : StepsBelow A A := fun _ _ h1 h2 => absurd h2 (by omega)

/-- **A halt from a wide clean tape passes through a clean tape that is cut at every depth.**  If every clean tape of
even width in [A, B) reaches a wider one (`StepsBelow A B`), and the machine halts T steps after a clean tape of even
width W ≥ A, then it reaches a clean tape of some even width W' ≥ W, W' ≥ B, with W'/2 in a cut class of the
clean-tape tree over the widths ≥ B (`cleanTreeG B d`) at every depth, and halts from there. -/
theorem clean_chain (A B : Nat) (h6 : 6 ≤ A) (hAB : A ≤ B) (hB : StepsBelow A B) (T : Nat) :
    ∀ (W : Nat), W % 2 = 0 → A ≤ W →
    steps T (roundStart [⟨.M, W - 2⟩] W) = none →
    ∃ W' k, W ≤ W' ∧ B ≤ W' ∧ W' % 2 = 0 ∧ (∀ d, (cleanTreeG B d).cutMem [(W' : Int) / 2, 0] = true) ∧
      steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.M, W' - 2⟩] W') ∧
      steps (T - k) (roundStart [⟨.M, W' - 2⟩] W') = none := by
  induction T using Nat.strongRecOn with
  | ind T ih =>
    intro W hW hA hT
    have hG6 : 6 ≤ W := by omega
    by_cases hstop : B ≤ W ∧ ∀ d, (cleanTreeG B d).cutMem [(W : Int) / 2, 0] = true
    · exact ⟨W, 0, Nat.le_refl _, hstop.1, hW, hstop.2, rfl, by simpa using hT⟩
    have hstep : ∃ n k W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound [⟨.M, W' - 2⟩] W' ∧
        steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.M, W' - 2⟩] W') ∧ 0 < n ∧ W < W' := by
      by_cases hb : W < B
      · exact hB W hW hA hb
      obtain ⟨d, hd⟩ := Classical.not_forall.mp (fun hall => hstop ⟨by omega, hall⟩)
      obtain ⟨n, k, ms', W', hr, hk, hc⟩ := clean_tree_step_G B d W (by omega) hW (by omega)
      rcases hc with hc | ⟨hn, rfl, hlt⟩
      · exact absurd hc hd
      · exact ⟨n, k, W', hr, hk, hn, hlt⟩
    obtain ⟨n, k, W', hr, hk, -, hlt⟩ := hstep
    have hwf : roundWF [⟨.M, W - 2⟩] W := roundWF_one.mpr ⟨hG6, hW⟩
    obtain ⟨-, -, hwf'⟩ := rounds_run 1000 n _ _ hwf (by rw [hr]; intro h; cases h)
    rw [hr] at hwf'
    have hW' : 6 ≤ W' ∧ W' % 2 = 0 := roundWF_one.mp hwf'
    obtain ⟨hle, hT'⟩ := steps_none_split hT hk
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0
        simp only [steps, Option.some.injEq] at hk
        exact absurd hk (roundStart_one_ne W W' hG6 hlt hW hW'.2)
      · exact h0
    obtain ⟨W'', k'', h1, h2, h3, h4, h5, h6⟩ := ih (T - k) (by omega) W' hW'.2 (by omega) hT'
    refine ⟨W'', k + k'', by omega, h2, h3, h4, steps_seq hk h5, ?_⟩
    rw [show T - (k + k'') = T - k - k'' by omega]
    exact h6

/-- **A halt from blank tape, after a prefix.**  If the run from blank tape reaches the clean tape of even width
W₀ ≥ A after k₀ steps, every clean tape of even width in [A, B) reaches a wider one (`StepsBelow A B`), and the machine
halts after T steps, then it first reaches a clean tape of even width W ≥ W₀, W ≥ B, with W/2 in the cut classes of the
clean-tape tree over the widths ≥ B (`cleanTreeG B d`) at every depth, and halts from that clean tape; and the mark
model, run from that clean tape, reaches a stuck configuration. -/
theorem blank_halt_clean_from (A B W₀ k₀ : Nat) (h6 : 6 ≤ A) (hAB : A ≤ B) (hB : StepsBelow A B)
    (hW₀ : W₀ % 2 = 0) (hAW₀ : A ≤ W₀) (hk₀ : steps k₀ ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W₀ - 2⟩] W₀))
    (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∃ W k, W₀ ≤ W ∧ B ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTreeG B d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t) := by
  obtain ⟨-, hT₀⟩ := steps_none_split hT hk₀
  obtain ⟨W, k, hle, hBW, hW, hcut, hk, hTW⟩ := clean_chain A B h6 hAB hB (T - k₀) W₀ hW₀ hAW₀ hT₀
  have hG6 : 6 ≤ W := by omega
  obtain ⟨t, ht, htw, hts⟩ := round_halt_needs_contact [⟨.M, W - 2⟩] W _ (roundWF_one.mpr ⟨hG6, hW⟩)
    (noG_one _) hTW
  refine ⟨W, k₀ + k, hle, hBW, hW, hcut, steps_seq hk₀ hk, ?_, t, ht, htw, stuck_cases hts⟩
  rw [show T - (k₀ + k) = T - k₀ - k by omega]
  exact hTW

/-- **What a halt from blank tape needs: a clean tape cut at every depth.**  If the machine, started on blank tape,
halts after T steps, then it first reaches a clean tape (gap, then only the end marker) of even width W ≥ 2³² with W/2
in a cut class of the clean-tape tree at every depth, and halts from that clean tape; and the mark model, run from
that clean tape, reaches a stuck configuration: a close at the right end (`EndClose`: the gap meets the end marker at
distance 0, or touches a block at the end) or an interior contact. -/
theorem blank_halt_clean (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∃ W k, prefixWidth ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTree d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t) := by
  obtain ⟨k₀, hk₀⟩ := blank_prefix
  obtain ⟨W, k, hle, -, h⟩ := blank_halt_clean_from cleanGamma cleanGamma prefixWidth k₀ (by decide)
    (Nat.le_refl _) (stepsBelow_self _) (by decide) (by decide) hk₀ T hT
  exact ⟨W, k, hle, h⟩

/-- **What a halt from blank tape needs, checked by the kernel alone.**  `blank_halt_clean` from the clean tape of
width 2²⁰ that the kernel's prefix reaches (`blank_prefix_kernel`), with the clean-tape tree over the widths ≥ 2²⁰
(`cleanTreeG kernelPrefixWidth d`): if the machine, started on blank tape, halts after T steps, then it first reaches a
clean tape of even width W ≥ 2²⁰ with W/2 in a cut class of that tree at every depth, and halts from that clean tape;
and the mark model, run from that clean tape, reaches a stuck configuration. -/
theorem blank_halt_clean_kernel (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∃ W k, kernelPrefixWidth ≤ W ∧ W % 2 = 0 ∧
      (∀ d, (cleanTreeG kernelPrefixWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t) := by
  obtain ⟨k₀, hk₀⟩ := blank_prefix_kernel
  obtain ⟨W, k, hle, -, h⟩ := blank_halt_clean_from kernelPrefixWidth kernelPrefixWidth kernelPrefixWidth k₀
    (by decide) (Nat.le_refl _) (stepsBelow_self _) (by decide) (Nat.le_refl _) hk₀ T hT
  exact ⟨W, k, hle, h⟩

/-- **What a halt from blank tape needs after a pass start.**  If the machine, started on blank tape, halts after T
steps, then from every phase-0 pass start it passes on its way with every gap at least 448 (`PassStart448`, right end
R, left countdown L₁ = `passL1 ms W`), its run follows the loop's chain (`LoopChain`): full passes (R → R/16,
L₁ → L₁/64), round-7 breaks and a half pass (only as the first step), each close-free with its exact map on the width,
the right end and the left countdown (`StepMap`), each to a pass start with gaps again all ≥ 448, to the last of them
(right end R₁); and the halt needs a stuck configuration after it: either right there, with R₁ in the closing set and
the left countdown in R₁'s class (`InCloseClass`; then R³/L₁² ≤ 176³/256² at the start of the chain's last run of
full passes, `LoopChain.sigma`), or after a further close-free stretch to where the run leaves the chain
(`LoopEnd`). -/
theorem blank_halt_loop (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∀ (R : Nat) (ms : List Mark) (W k : Nat), PassStart448 ms W R →
      steps k ⟨blank, blank, .A⟩ = some (roundStart ms W) →
      ∃ ks ms₁ W₁ R₁, LoopChain ms W R ks ms₁ W₁ R₁ ∧
        ((InCloseClass ms₁ W₁ R₁ ∧ ∃ t, Reach ⟨[], 1, ms₁, W₁⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
          ∃ n ms' W', roundsZ 1000 n ms₁ W₁ = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n ms₁ W₁, 3 ≤ d) ∧
            LoopEnd W₁ R₁ (passL1 ms₁ W₁) n (meetsRounds 1000 n ms₁ W₁) ms' W' ∧
            ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) := by
  intro R ms W k hP hk
  obtain ⟨-, hT'⟩ := steps_none_split hT hk
  exact loop_chain_halt _ R ms W hP hT'

/-- **The σ bound, from blank tape.**  If the machine, started on blank tape, halts after T steps, then at no phase-0
pass start it passes on its way with every gap at least 448 and R³/L₁² > 176³/256² (with s = log₂(W/R),
λ = log₂(|L₁|/W) and σ = 3s + 2λ there: log₂W > σ + 6.38) does it close through full passes alone: the loop's chain
from there either makes a half pass or a round-7 break before it reaches a closing class, or it ends (`LoopEnd`), and
the halt needs a stuck configuration after that. -/
theorem blank_halt_sigma (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∀ (R : Nat) (ms : List Mark) (W k : Nat), PassStart448 ms W R → ¬ SigmaOK R (passL1 ms W) →
      steps k ⟨blank, blank, .A⟩ = some (roundStart ms W) →
      ∃ ks ms₁ W₁ R₁, LoopChain ms W R ks ms₁ W₁ R₁ ∧
        ((InCloseClass ms₁ W₁ R₁ ∧ (StepKind.half ∈ ks ∨ StepKind.break7 ∈ ks) ∧
            ∃ t, Reach ⟨[], 1, ms₁, W₁⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
          ∃ n ms' W', roundsZ 1000 n ms₁ W₁ = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n ms₁ W₁, 3 ≤ d) ∧
            LoopEnd W₁ R₁ (passL1 ms₁ W₁) n (meetsRounds 1000 n ms₁ W₁) ms' W' ∧
            ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) := by
  intro R ms W k hP hσ hk
  obtain ⟨-, hT'⟩ := steps_none_split hT hk
  exact loop_halt_sigma R ms W hP hσ _ hT'

/-- **Wide pass starts, from blank tape.**  If the machine, started on blank tape, halts after T steps, then from every
phase-0 pass start it passes on its way with width W ≥ 2²⁷ and every gap at least 448, the loop's chain either ends
(`LoopEnd`) and the halt needs a stuck configuration after that, or it reaches a closing class without a round-7
break: through p full passes (R = 16^p R₁, L₁ = 64^p L₁′), or a half pass from W ≡ 2 (mod 4) and then p full passes
(R = 2 · 16^p R₁, 2 · 64^p L₁′ = L₁ + 35 W − 147 R − 60), and the halt needs a stuck configuration after it. -/
theorem blank_halt_wide (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∀ (R : Nat) (ms : List Mark) (W k : Nat), PassStart448 ms W R → 2 ^ 27 ≤ W →
      steps k ⟨blank, blank, .A⟩ = some (roundStart ms W) →
      ∃ ks ms₁ W₁ R₁, LoopChain ms W R ks ms₁ W₁ R₁ ∧
        ((InCloseClass ms₁ W₁ R₁ ∧
            (∃ p, (ks = List.replicate p .full ∧ R = 16 ^ p * R₁ ∧ passL1 ms W = 64 ^ p * passL1 ms₁ W₁) ∨
              (ks = .half :: List.replicate p .full ∧ W % 4 = 2 ∧ R = 2 * 16 ^ p * R₁ ∧
                2 * 64 ^ p * passL1 ms₁ W₁ = passL1 ms W + 35 * (W : Int) - 147 * (R : Int) - 60)) ∧
            ∃ t, Reach ⟨[], 1, ms₁, W₁⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
          ∃ n ms' W', roundsZ 1000 n ms₁ W₁ = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n ms₁ W₁, 3 ≤ d) ∧
            LoopEnd W₁ R₁ (passL1 ms₁ W₁) n (meetsRounds 1000 n ms₁ W₁) ms' W' ∧
            ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) := by
  intro R ms W k hP hW hk
  obtain ⟨-, hT'⟩ := steps_none_split hT hk
  exact loop_halt_wide R ms W hP hW _ hT'

/-- **What a halt from blank tape needs after a loop state.**  If the machine, started on blank tape, halts after T
steps, then every loop state it passes on its way (walls at a, b, c, width E; a odd, b even, c odd, E even; every gap
≥ 390) is followed by the certified exit stretch (`exit_stretch`), close-free and with every end meeting at distance at
least 3, to where it ends (`ExitEvent`: a clean tape, a break of the end-meeting chain, or a loop state again after a
full pass), and the halt needs a stuck configuration after it: a close at the right end or an interior contact. -/
theorem blank_halt_exit (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∀ (a b c E k : Nat), a % 2 = 1 → b % 2 = 0 → c % 2 = 1 → E % 2 = 0 →
      390 ≤ a → a + 390 ≤ b → b + 390 ≤ c → c + 390 ≤ E →
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E) →
      ∃ n ms' W', roundsZ 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E = .newRound ms' W' ∧
        (∀ d ∈ meetsRounds 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E, 3 ≤ d) ∧
        ExitEvent n (meetsRounds 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E) ms' W' ∧
        ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t) := by
  intro a b c E k ha hb hc hE h1 h2 h3 h4 hk
  obtain ⟨-, hT'⟩ := steps_none_split hT hk
  exact exit_halt_needs_contact a b c E ha hb hc hE h1 h2 h3 h4 _ hT'

/-- **End to end: what a halt from blank tape needs.**  `blank_halt_clean`, `blank_halt_loop` and `blank_halt_exit`
together: if the machine, started on blank tape, halts after T steps, then

1. it first reaches a clean tape (gap, then only the end marker) of even width W ≥ 2³² with W/2 in a cut class of
   the clean-tape tree at every depth, and halts from that clean tape;
2. the mark model, run from that clean tape, reaches a stuck configuration: a close at the right end
   (`EndClose`: the gap meets the end marker at distance 0, or touches a block at the end) or an interior contact;
3. from every phase-0 pass start the machine passes on its way (walls at a, b, E − R − 1, width E, the parities,
   every gap ≥ 448: `PassStart448`; left countdown L₁ = 147 b + 280 E − 392 (E − R − 1) − 578), the run follows the
   loop's chain (`LoopChain`): full passes, round-7 breaks and a half pass (only as the first step), each close-free
   with its exact map on the width, the right end and the left countdown, each to a pass start with gaps again all
   ≥ 448, to the last of them (right end R₁), and the halt needs a stuck configuration after it: either right there,
   with R₁ in the closing set {2, 4, 8, 16, 24, 32, 48, 64, 176} and the left countdown in R₁'s class
   (`InCloseClass`), or after a further close-free stretch to where the run leaves the chain (`LoopEnd`: a round start
   that is not three walls after the run left phase 0 or the halving chain, or a landing with a gap below 448);
4. every loop state the machine passes on its way (walls at a, b, c, width E, the parities, every gap ≥ 390) is
   followed by the certified exit stretch, to a clean tape, a break of the end-meeting chain or a loop state again
   (`ExitEvent`), and the halt needs a stuck configuration after it. -/
theorem blank_halt_structure (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    (∃ W k, prefixWidth ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTree d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∧
    (∀ (R : Nat) (ms : List Mark) (W k : Nat), PassStart448 ms W R →
      steps k ⟨blank, blank, .A⟩ = some (roundStart ms W) →
      ∃ ks ms₁ W₁ R₁, LoopChain ms W R ks ms₁ W₁ R₁ ∧
        ((InCloseClass ms₁ W₁ R₁ ∧ ∃ t, Reach ⟨[], 1, ms₁, W₁⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
          ∃ n ms' W', roundsZ 1000 n ms₁ W₁ = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n ms₁ W₁, 3 ≤ d) ∧
            LoopEnd W₁ R₁ (passL1 ms₁ W₁) n (meetsRounds 1000 n ms₁ W₁) ms' W' ∧
            ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t))) ∧
    (∀ (a b c E k : Nat), a % 2 = 1 → b % 2 = 0 → c % 2 = 1 → E % 2 = 0 →
      390 ≤ a → a + 390 ≤ b → b + 390 ≤ c → c + 390 ≤ E →
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E) →
      ∃ n ms' W', roundsZ 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E = .newRound ms' W' ∧
        (∀ d ∈ meetsRounds 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E, 3 ≤ d) ∧
        ExitEvent n (meetsRounds 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E) ms' W' ∧
        ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) :=
  ⟨blank_halt_clean T hT, blank_halt_loop T hT, blank_halt_exit T hT⟩

/-- **End to end, checked by the kernel alone.**  `blank_halt_structure` with item 1 from the kernel's prefix
(`blank_halt_clean_kernel`): the clean tape a halt needs is at least 2²⁰ wide, and W/2 lies in a cut class of the
clean-tape tree over the widths ≥ 2²⁰ at every depth; items 2 to 4 as there.  Nothing here is evaluated by compiled
code. -/
theorem blank_halt_structure_kernel (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    (∃ W k, kernelPrefixWidth ≤ W ∧ W % 2 = 0 ∧
      (∀ d, (cleanTreeG kernelPrefixWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∧
    (∀ (R : Nat) (ms : List Mark) (W k : Nat), PassStart448 ms W R →
      steps k ⟨blank, blank, .A⟩ = some (roundStart ms W) →
      ∃ ks ms₁ W₁ R₁, LoopChain ms W R ks ms₁ W₁ R₁ ∧
        ((InCloseClass ms₁ W₁ R₁ ∧ ∃ t, Reach ⟨[], 1, ms₁, W₁⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
          ∃ n ms' W', roundsZ 1000 n ms₁ W₁ = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n ms₁ W₁, 3 ≤ d) ∧
            LoopEnd W₁ R₁ (passL1 ms₁ W₁) n (meetsRounds 1000 n ms₁ W₁) ms' W' ∧
            ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t))) ∧
    (∀ (a b c E k : Nat), a % 2 = 1 → b % 2 = 0 → c % 2 = 1 → E % 2 = 0 →
      390 ≤ a → a + 390 ≤ b → b + 390 ≤ c → c + 390 ≤ E →
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E) →
      ∃ n ms' W', roundsZ 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E = .newRound ms' W' ∧
        (∀ d ∈ meetsRounds 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E, 3 ≤ d) ∧
        ExitEvent n (meetsRounds 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E) ms' W' ∧
        ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) :=
  ⟨blank_halt_clean_kernel T hT, blank_halt_loop T hT, blank_halt_exit T hT⟩

/-- **The open question, reduced.**  If the machine does not halt from any clean tape of even width W ≥ 2³² with W/2
in a cut class of the clean-tape tree at every depth, then it does not halt from blank tape. -/
theorem never_halts_of_cut_classes
    (h : ∀ W, prefixWidth ≤ W → W % 2 = 0 → (∀ d, (cleanTree d).cutMem [(W : Int) / 2, 0] = true) →
      ∀ T, steps T (roundStart [⟨.M, W - 2⟩] W) ≠ none) :
    ∀ T, steps T ⟨blank, blank, .A⟩ ≠ none := by
  intro T hT
  obtain ⟨W, k, hle, hW, hcut, -, hTW, -⟩ := blank_halt_clean T hT
  exact h W hle hW hcut (T - k) hTW

/-- **The open question, reduced, checked by the kernel alone.**  If the machine does not halt from any clean tape of
even width W ≥ 2²⁰ with W/2 in a cut class of the clean-tape tree over the widths ≥ 2²⁰ at every depth, then it does
not halt from blank tape. -/
theorem never_halts_of_cut_classes_kernel
    (h : ∀ W, kernelPrefixWidth ≤ W → W % 2 = 0 →
      (∀ d, (cleanTreeG kernelPrefixWidth d).cutMem [(W : Int) / 2, 0] = true) →
      ∀ T, steps T (roundStart [⟨.M, W - 2⟩] W) ≠ none) :
    ∀ T, steps T ⟨blank, blank, .A⟩ ≠ none := by
  intro T hT
  obtain ⟨W, k, hle, hW, hcut, -, hTW, -⟩ := blank_halt_clean_kernel T hT
  exact h W hle hW hcut (T - k) hTW

#print axioms blank_halt_clean
#print axioms blank_halt_sigma
#print axioms blank_halt_wide
#print axioms blank_halt_exit
#print axioms blank_halt_structure
#print axioms never_halts_of_cut_classes
#print axioms blank_halt_structure_kernel
#print axioms never_halts_of_cut_classes_kernel

end BB6
