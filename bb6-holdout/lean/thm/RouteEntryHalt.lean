import RouteEntryTheorem
import LoopHalt
open BB6 BB6.Sym

/-! # The routes do not close the loop where they enter it

`route_tree_entry` (`thm/RouteEntryTheorem.lean`) ends every path of the route tree with loop entries at a clean tape,
at a pass start from which no point of the class closes through the loop (`EntryNoClose`), or in a cut class.  This
file adds the loop's chain (`loop_halt_leaves`, `thm/LoopHalt.lean`): from a pass start of width at least 2²⁴ a close
through the loop is p full passes, after at most one half pass at the start, and `EntryNoClose` excludes both (the
left countdown at a close is in the class of its right end and ≡ 3 mod 7, `loopL1_mod7`; `EntryNoClose.no_close`).
With the middle wall at least 896 below the width when W ≡ 2 mod 4, every landing of the chain is again a pass start
with every gap at least 448.  So a halt from such a pass start needs the loop's chain to end without a close where the
run leaves three walls, and a stuck configuration after that (`entry_halt`); and a halt from a two-marker state with
wide gaps needs, unless the start is in a cut class of the tree, a halt from the next clean tape, or that
(`route_halt`). -/

/-- The table of `NoCloseAt` is the closing set of the endgame trees with its classes. -/
theorem closeTable_eq : closeTable = closeClasses := rfl

theorem closeClass_mem {R : Nat} {m c : Int} (h : closeClass R = some (m, c)) : (R, m, c) ∈ closeTable := by
  unfold closeClass at h
  cases hf : closeClasses.find? (·.1 == R) with
  | none => rw [hf] at h; cases h
  | some x =>
    rw [hf] at h
    obtain ⟨x1, x2⟩ := x
    simp only [Option.map_some, Option.some.injEq] at h
    have hx := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [beq_iff_eq] at hp
    subst hp h
    exact hx

/-- **A loop entry that cannot close reaches no closing class.**  The loop's chain from a pass start of
`EntryNoClose` never ends in a closing class: from a width at least 2²⁴ such a chain is p full passes, after at most
one half pass (`LoopChain.close_wide`), and `EntryNoClose` excludes both. -/
theorem BB6.Sym.EntryNoClose.no_close {ms : List Mark} {W : Nat} (h : EntryNoClose ms W) {R : Nat}
    {ks : List StepKind} {ms₁ : List Mark} {W₁ R₁ : Nat} (hch : LoopChain ms W R ks ms₁ W₁ R₁)
    (hc : InCloseClass ms₁ W₁ R₁) : False := by
  obtain ⟨hW, R', a, b, rfl, hP', -, hfull, hhalf⟩ := h
  -- the chain's right end is the entry's: both are the distance of the last wall from the end
  have hR : R = R' := by
    obtain ⟨a₂, b₂, e₂, -, -, -, -, -, -, -, h₂⟩ := hch.start
    obtain ⟨a₃, b₃, e₃, -, -, -, -, -, -, -, h₃⟩ := hP'
    simp only [List.cons.injEq, Mark.mk.injEq, true_and, and_true] at e₂ e₃
    omega
  subst hR
  obtain ⟨p, hp⟩ := hch.close_wide hc hW
  obtain ⟨a₁, b₁, m, c, rfl, hcc, hl⟩ := hc
  have hmem := closeClass_mem hcc
  have h7 : passL1 [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁ % 7 = 3 := loopL1_mod7 _ _ _
  have hlm : passL1 [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁ % m = c := hl
  rcases hp with ⟨-, hR, hL⟩ | ⟨-, hW4, hR, hL⟩
  · exact hfull p R₁ m c _ hmem (by rw [hR]; push_cast; rfl) hL hlm h7
  · exact hhalf hW4 _ _ (by rw [hR]; push_cast; rw [Int.mul_assoc]) (by rw [← hL, Int.mul_assoc]) p R₁ m c _
      hmem rfl rfl hlm h7

/-- **From a loop entry that cannot close, a halt needs the loop's chain to end first.**  If the machine halts from a
pass start of `EntryNoClose` (every gap at least 448, width at least 2²⁴, the middle wall at least 896 below the width
when W ≡ 2 mod 4, and no close after full passes or after a half pass and full passes), then the loop's chain from
there (`LoopChain`) reaches no closing class: it ends, close-free, where the run has left phase 0 or the halving chain
at a round start that is not three walls, and the mark model reaches a stuck configuration after that. -/
theorem entry_halt {ms : List Mark} {W : Nat} (h : EntryNoClose ms W) (T : Nat)
    (hT : steps T (roundStart ms W) = none) :
    ∃ R ks ms₁ W₁ R₁, PassStart448 ms W R ∧ LoopChain ms W R ks ms₁ W₁ R₁ ∧
      ∃ n ms' W', roundsZ 1000 n ms₁ W₁ = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n ms₁ W₁, 3 ≤ d) ∧
        (LeftPhase0 n ms' ∨ ChainBreak (meetsRounds 1000 n ms₁ W₁)) ∧ NotWWW ms' ∧
        ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t) := by
  obtain ⟨hW, R, a, b, rfl, hP, hh, -⟩ := id h
  obtain ⟨ks, ms₁, W₁, R₁, hch, ⟨hc, -⟩ | he⟩ := loop_halt_leaves R a b W hP hW hh T hT
  · exact (h.no_close hch hc).elim
  · exact ⟨R, ks, ms₁, W₁, R₁, hP, hch, he⟩

/-- **A halt from a two-marker state with wide gaps does not close the loop where the route enters it.**  For every
Γ ≥ 8, every depth d, and all naturals m, E with m even, E odd and both gaps at least Γ, if the machine halts T steps
after the round start G 1, M m, M E − 2 (width E), then either (m/2, (E − 1)/2) lies in a cut class of
`routeTreeE Γ d`, or the machine runs n rounds of the mark model (k steps) to a round start from which it halts, and
that round start is a clean tape reached after at least one round, or a phase-0 pass start with every gap at least
448 and width at least 2²⁴ from which the loop's chain ends without a close, where the run leaves three walls, and the
halt needs a stuck configuration after that. -/
theorem route_halt (Γ d m E : Nat) (hΓ : 8 ≤ Γ) (hm : m % 2 = 0) (hE : E % 2 = 1) (h1 : Γ ≤ m) (h2 : m + Γ ≤ E)
    (T : Nat) (hT : steps T (roundStart [⟨.M, m⟩, ⟨.M, E - 2⟩] E) = none) :
    (routeTreeE Γ d).cutMem [(m : Int) / 2, ((E : Int) - 1) / 2] = true ∨
    ∃ n k ms' W', roundsZ 1000 n [⟨.M, m⟩, ⟨.M, E - 2⟩] E = .newRound ms' W' ∧
      steps k (roundStart [⟨.M, m⟩, ⟨.M, E - 2⟩] E) = some (roundStart ms' W') ∧
      steps (T - k) (roundStart ms' W') = none ∧
      ((0 < n ∧ cleanTape ms' W') ∨
        ∃ R ks ms₁ W₁ R₁, PassStart448 ms' W' R ∧ 2 ^ 24 ≤ W' ∧ LoopChain ms' W' R ks ms₁ W₁ R₁ ∧
          ∃ n₂ ms'' W'', roundsZ 1000 n₂ ms₁ W₁ = .newRound ms'' W'' ∧ (∀ d ∈ meetsRounds 1000 n₂ ms₁ W₁, 3 ≤ d) ∧
            (LeftPhase0 n₂ ms'' ∨ ChainBreak (meetsRounds 1000 n₂ ms₁ W₁)) ∧ NotWWW ms'' ∧
            ∃ t, Reach ⟨[], 1, ms'', W''⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) := by
  obtain ⟨n, k, ms', W', h1', h2', h3'⟩ := route_tree_entry Γ d m E hΓ hm hE h1 h2
  rcases h3' with hc | hc | hc
  · exact Or.inl hc
  · obtain ⟨-, hT'⟩ := steps_none_split hT h2'
    exact Or.inr ⟨n, k, ms', W', h1', h2', hT', Or.inl hc⟩
  · obtain ⟨-, hT'⟩ := steps_none_split hT h2'
    obtain ⟨R, ks, ms₁, W₁, R₁, hP, hch, he⟩ := entry_halt hc _ hT'
    exact Or.inr ⟨n, k, ms', W', h1', h2', hT', Or.inr ⟨R, ks, ms₁, W₁, R₁, hP, hc.1, hch, he⟩⟩

/-- **The routes, from blank tape.**  If the machine, started on blank tape, halts after T steps, then at every
two-marker state G 1, M m, M E − 2 (width E) that it passes on its way with both gaps at least Γ ≥ 8, either
(m/2, (E − 1)/2) lies in a cut class of `routeTreeE Γ d` at every depth d, or the machine runs n rounds of the mark
model from there to a round start from which it halts, and that round start is the next clean tape, or a loop entry
(a phase-0 pass start with every gap at least 448 and width at least 2²⁴) from which the loop's chain ends without a
close, where the run leaves three walls, and the halt needs a stuck configuration after that. -/
theorem blank_halt_route (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∀ (Γ m E k : Nat), 8 ≤ Γ → m % 2 = 0 → E % 2 = 1 → Γ ≤ m → m + Γ ≤ E →
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, m⟩, ⟨.M, E - 2⟩] E) →
      (∀ d, (routeTreeE Γ d).cutMem [(m : Int) / 2, ((E : Int) - 1) / 2] = true) ∨
      ∃ n k' ms' W', roundsZ 1000 n [⟨.M, m⟩, ⟨.M, E - 2⟩] E = .newRound ms' W' ∧
        steps k' (roundStart [⟨.M, m⟩, ⟨.M, E - 2⟩] E) = some (roundStart ms' W') ∧
        steps (T - k - k') (roundStart ms' W') = none ∧
        ((0 < n ∧ cleanTape ms' W') ∨
          ∃ R ks ms₁ W₁ R₁, PassStart448 ms' W' R ∧ 2 ^ 24 ≤ W' ∧ LoopChain ms' W' R ks ms₁ W₁ R₁ ∧
            ∃ n₂ ms'' W'', roundsZ 1000 n₂ ms₁ W₁ = .newRound ms'' W'' ∧ (∀ d ∈ meetsRounds 1000 n₂ ms₁ W₁, 3 ≤ d) ∧
              (LeftPhase0 n₂ ms'' ∨ ChainBreak (meetsRounds 1000 n₂ ms₁ W₁)) ∧ NotWWW ms'' ∧
              ∃ t, Reach ⟨[], 1, ms'', W''⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) := by
  intro Γ m E k hΓ hm hE h1 h2 hk
  obtain ⟨-, hT'⟩ := steps_none_split hT hk
  by_cases hall : ∀ d, (routeTreeE Γ d).cutMem [(m : Int) / 2, ((E : Int) - 1) / 2] = true
  · exact Or.inl hall
  · obtain ⟨d, hd⟩ := Classical.not_forall.mp hall
    rcases route_halt Γ d m E hΓ hm hE h1 h2 (T - k) hT' with hc | h
    · exact absurd hc hd
    · exact Or.inr h

#print axioms BB6.Sym.EntryNoClose.no_close
#print axioms entry_halt
#print axioms route_halt
#print axioms blank_halt_route
