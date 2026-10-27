import Prefix
import CleanTheorem
import LoopHalt
import ExitHalt

/-!
# End to end: what a halt of the machine from blank tape needs

The pieces, all theorems about the machine `1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE` started on blank tape:

* `blank_prefix` (`thm/Prefix.lean`): the machine reaches the one-marker clean tape of width 2³² without halting.
* `clean_tree_step` (`thm/CleanTheorem.lean`): for every depth d, from every clean tape of width W ≥ 2³², the machine
  reaches a wider clean tape without halting, unless W/2 lies in one of the cut classes of the depth-d clean-tape tree
  (`cleanTree d`, built by the proved explorer of `BB6/RouteExplore.lean`, so nothing is evaluated).
* `round_halt_needs_contact`, `stuck_cases` (`BB6/HaltClose`, `BB6/HaltStretch`): a halt from a round start needs
  the mark model, run from there, to reach a stuck configuration: a close at the right end or an interior contact.
* `loop_halt_needs_contact` (`thm/LoopHalt.lean`): a halt from a phase-0 pass start whose R is outside the closing set
  comes only after the close-free stretch the loop's trees certify from it, and needs a stuck configuration after that
  stretch.
* `exit_halt_needs_contact` (`thm/ExitHalt.lean`): the same after a loop state's exit stretch.

`clean_chain` chains the clean-tape steps by strong induction on the halting time (a run from a clean tape to a wider
one takes at least one step, `roundStart_one_ne`): at each clean tape, either it is in the cut classes at every depth,
or some depth decides it and the run goes on to a wider clean tape.  `blank_halt_clean` adds the prefix and the stuck
configuration, `blank_halt_loop` the pass starts, `blank_halt_exit` the loop states, and `blank_halt_structure` is
the three together.  `blank_halt_clean_from` is `blank_halt_clean` for any bound B below which every clean tape
reaches a wider one (`thm/EndToEndDirect.lean` uses it with B = 2⁴¹).

**What is not claimed.**  Nothing is said about the clean tapes that are in the cut classes at every depth: whether
the machine halts from one of them is exactly what remains open.  At each depth d the cut classes are residue classes
of W/2 modulo powers of two up to 2^d; their measure is evaluated in `thm/CleanMass.lean` (2.4 × 10⁻⁵ at 36 digits),
and the clean tape a halt needs lies in all of them.
-/

namespace BB6
open BB6.Sym

theorem noG_one (W : Nat) : noG [⟨.M, W⟩] := by
  intro m hm
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
  subst hm; simp

/-- Every clean tape of even width in [`cleanGamma`, B) reaches a wider one-marker clean tape. -/
def StepsBelow (B : Nat) : Prop :=
  ∀ W, W % 2 = 0 → cleanGamma ≤ W → W < B →
    ∃ n k W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound [⟨.M, W' - 2⟩] W' ∧
      steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.M, W' - 2⟩] W') ∧ 0 < n ∧ W < W'

theorem stepsBelow_gamma : StepsBelow cleanGamma := fun _ _ h1 h2 => absurd h2 (by omega)

/-- **A halt from a wide clean tape passes through a clean tape that is cut at every depth.**  If every clean tape of
even width in [`cleanGamma`, B) reaches a wider one (`StepsBelow B`), and the machine halts T steps after a clean
tape of even width W ≥ `cleanGamma`, then it reaches a clean tape of some even width W' ≥ W, W' ≥ B, with W'/2 in a
cut class of the clean-tape tree over the widths ≥ B (`cleanTreeG B d`) at every depth, and halts from there. -/
theorem clean_chain (B : Nat) (h6 : 6 ≤ B) (hB : StepsBelow B) (T : Nat) : ∀ (W : Nat), W % 2 = 0 → cleanGamma ≤ W →
    steps T (roundStart [⟨.M, W - 2⟩] W) = none →
    ∃ W' k, W ≤ W' ∧ B ≤ W' ∧ W' % 2 = 0 ∧ (∀ d, (cleanTreeG B d).cutMem [(W' : Int) / 2, 0] = true) ∧
      steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.M, W' - 2⟩] W') ∧
      steps (T - k) (roundStart [⟨.M, W' - 2⟩] W') = none := by
  induction T using Nat.strongRecOn with
  | ind T ih =>
    intro W hW hG hT
    have hG6 : 6 ≤ W := by simp only [cleanGamma] at hG; omega
    by_cases hstop : B ≤ W ∧ ∀ d, (cleanTreeG B d).cutMem [(W : Int) / 2, 0] = true
    · exact ⟨W, 0, Nat.le_refl _, hstop.1, hW, hstop.2, rfl, by simpa using hT⟩
    have hstep : ∃ n k W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound [⟨.M, W' - 2⟩] W' ∧
        steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.M, W' - 2⟩] W') ∧ 0 < n ∧ W < W' := by
      by_cases hb : W < B
      · exact hB W hW hG hb
      obtain ⟨d, hd⟩ := Classical.not_forall.mp (fun hall => hstop ⟨by omega, hall⟩)
      obtain ⟨n, k, ms', W', hr, hk, hc⟩ := clean_tree_step_G B d W h6 hW (by omega)
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

/-- `blank_halt_clean` for any bound B below which every clean tape of width ≥ 2³² reaches a wider one: the clean
tape a halt needs is at least B wide, and in the cut classes of the tree over the widths ≥ B at every depth. -/
theorem blank_halt_clean_from (B : Nat) (h6 : 6 ≤ B) (hB : StepsBelow B) (T : Nat)
    (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∃ W k, prefixWidth ≤ W ∧ B ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTreeG B d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t) := by
  obtain ⟨k₀, hk₀⟩ := blank_prefix
  obtain ⟨-, hT₀⟩ := steps_none_split hT hk₀
  obtain ⟨W, k, hle, hBW, hW, hcut, hk, hTW⟩ :=
    clean_chain B h6 hB (T - k₀) prefixWidth (by decide) (by decide) hT₀
  have hG6 : 6 ≤ W := by simp only [prefixWidth] at hle; omega
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
  obtain ⟨W, k, hle, -, h⟩ := blank_halt_clean_from cleanGamma (by decide) stepsBelow_gamma T hT
  exact ⟨W, k, hle, h⟩

/-- **What a halt from blank tape needs after a pass start.**  If the machine, started on blank tape, halts after T
steps, then every phase-0 pass start it passes on its way (walls at a, b, E − R − 1, width E, the parities, every gap
≥ 448), whose R is outside the closing set {2, 4, 8, 16, 24, 32, 48, 64, 176}, is followed by a close-free stretch the
mark model covers through every pass of the loop, and the halt needs a stuck configuration after it. -/
theorem blank_halt_loop (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∀ (R a b E k : Nat), R % 2 = 0 → 2 ≤ R → closingSet.contains R = false →
      a % 2 = 1 → b % 2 = 0 → E % 2 = 0 → 448 ≤ a → a + 448 ≤ b → b + 448 + R + 1 ≤ E →
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E) →
      ∃ n ms' W', roundsZ 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E = .newRound ms' W' ∧
        (∀ d ∈ meetsRounds 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E, 3 ≤ d) ∧
        ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t) := by
  intro R a b E k hR hR2 hS ha hb hE h1 h2 h3 hk
  obtain ⟨-, hT'⟩ := steps_none_split hT hk
  exact loop_halt_needs_contact R hR hR2 hS a b E ha hb hE h1 h2 h3 _ hT'

/-- **What a halt from blank tape needs after a loop state.**  If the machine, started on blank tape, halts after T
steps, then every loop state it passes on its way (walls at a, b, c, width E; a odd, b even, c odd, E even; every gap
≥ 390) is followed by the certified exit stretch (`exit_no_halt`), and the halt needs a stuck configuration after it:
a close at the right end or an interior contact. -/
theorem blank_halt_exit (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∀ (a b c E k : Nat), a % 2 = 1 → b % 2 = 0 → c % 2 = 1 → E % 2 = 0 →
      390 ≤ a → a + 390 ≤ b → b + 390 ≤ c → c + 390 ≤ E →
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E) →
      ∃ n ms' W', roundsZ 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E = .newRound ms' W' ∧
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
3. every phase-0 pass start the machine passes on its way (walls at a, b, E − R − 1, width E, the parities, every gap
   ≥ 448), whose R is outside the closing set {2, 4, 8, 16, 24, 32, 48, 64, 176}, is followed by a close-free
   stretch the mark model covers through every pass of the loop, and the halt needs a stuck configuration after it;
4. every loop state the machine passes on its way (walls at a, b, c, width E, the parities, every gap ≥ 390) is
   followed by the certified exit stretch, and the halt needs a stuck configuration after it. -/
theorem blank_halt_structure (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    (∃ W k, prefixWidth ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTree d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∧
    (∀ (R a b E k : Nat), R % 2 = 0 → 2 ≤ R → closingSet.contains R = false →
      a % 2 = 1 → b % 2 = 0 → E % 2 = 0 → 448 ≤ a → a + 448 ≤ b → b + 448 + R + 1 ≤ E →
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E) →
      ∃ n ms' W', roundsZ 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E = .newRound ms' W' ∧
        (∀ d ∈ meetsRounds 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E, 3 ≤ d) ∧
        ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∧
    (∀ (a b c E k : Nat), a % 2 = 1 → b % 2 = 0 → c % 2 = 1 → E % 2 = 0 →
      390 ≤ a → a + 390 ≤ b → b + 390 ≤ c → c + 390 ≤ E →
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E) →
      ∃ n ms' W', roundsZ 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E = .newRound ms' W' ∧
        ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) :=
  ⟨blank_halt_clean T hT, blank_halt_loop T hT, blank_halt_exit T hT⟩

/-- **The open question, reduced.**  If the machine does not halt from any clean tape of even width W ≥ 2³² with W/2
in a cut class of the clean-tape tree at every depth, then it does not halt from blank tape. -/
theorem never_halts_of_cut_classes
    (h : ∀ W, prefixWidth ≤ W → W % 2 = 0 → (∀ d, (cleanTree d).cutMem [(W : Int) / 2, 0] = true) →
      ∀ T, steps T (roundStart [⟨.M, W - 2⟩] W) ≠ none) :
    ∀ T, steps T ⟨blank, blank, .A⟩ ≠ none := by
  intro T hT
  obtain ⟨W, k, hle, hW, hcut, -, hTW, -⟩ := blank_halt_clean T hT
  exact h W hle hW hcut (T - k) hTW

#print axioms blank_halt_clean
#print axioms blank_halt_exit
#print axioms blank_halt_structure
#print axioms never_halts_of_cut_classes

end BB6
