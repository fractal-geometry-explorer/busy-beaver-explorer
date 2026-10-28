import RouteEntryHalt
import CleanEntryTheorem
import LoopClose
import BB6.RouteEntryC
open BB6 BB6.Sym

/-! # The routes do not close the loop where they enter it, with the narrower closing classes

`thm/RouteEntryHalt.lean` with the closing classes of `closeClassC` (`thm/LoopClose.lean`) in place of those of
`closeClasses`.  `routeTreeEC` and `cleanTreeGEC` are the route tree and the clean-tape tree with loop entries, built by
the same explorers with the entry check of `closeTableC` (`entryOKC` and `cleanEntryOKC`, `BB6/RouteEntryC.lean`).  That
check passes wherever `entryOK` does, so these trees stop every path that `routeTreeE` and `cleanTreeGE` stop at a loop
entry, there or earlier, and they also stop paths at loop entries from which the loop could close only in a class of
`closeClasses` that is not one of `closeClassC`.  Elsewhere they are the same explorations, so their cut classes are
among those of the older trees.  From a loop entry of `EntryNoCloseC` the loop's chain reaches no class of `closeClassC`
(`EntryNoCloseC.no_close`: from a width ≥ 2²⁰ such a close is p full passes after at most one half pass,
`LoopChain.close_wideC`).  So with `loop_halt_leaves_close` a halt from the entry needs the loop's chain to end without
a close where the run leaves three walls, with the end meetings of its last stretch at distance at least 2, and a stuck
configuration after that (`entry_halt_close`); and a halt from a two-marker state with wide gaps needs, unless the start
is in a cut class of the tree, a halt from the next clean tape, or that (`route_halt_close`, `blank_halt_route_close`).
Nothing is evaluated. -/

/-! ## The trees with the narrower entry check -/

/-- The route tree with loop entries that cannot close in a class of `closeClassC`, with cone constant Γ and depth d
(a path is also cut after 10,000 rounds): `routeTreeE` with `entryOKC`. -/
def routeTreeEC (Γ d : Nat) : RTree :=
  RTree.exploreE Γ 1000 (entryOKC Γ) (10000 + d) d false rtStart.1 rtStart.2.1 rtStart.2.2

theorem route_tree_entryC_ok (Γ d : Nat) :
    (routeTreeEC Γ d).okE Γ 1000 (entryOKC Γ) false rtStart.1 rtStart.2.1 rtStart.2.2 = true :=
  RTree.exploreE_okE _ _ _ _ _ _ _ _ _

/-- **From a two-marker state with wide gaps, the machine reaches the next clean tape or a loop entry that cannot
close in a class of `closeClassC`, unless the start is in a cut class.**  `route_tree_entry` with `routeTreeEC`: for
every Γ ≥ 8, every depth d, and all naturals m, E with m even, E odd and both gaps at least Γ, the machine started from
the round start G 1, M m, M E − 2 (width E) runs n rounds of the mark model to a round start without halting, and either
n ≥ 1 and that round start is a clean tape, or it is a phase-0 pass start with every gap at least 448 and width at least
2²⁴ from which the loop cannot close in a class of `closeClassC` (`EntryNoCloseC`), or (m/2, (E − 1)/2) lies in one of
the cut classes of `routeTreeEC Γ d`. -/
theorem route_tree_entryC (Γ d m E : Nat) (hΓ : 8 ≤ Γ) (hm : m % 2 = 0) (hE : E % 2 = 1) (h1 : Γ ≤ m)
    (h2 : m + Γ ≤ E) :
    ∃ n k ms' W', roundsZ 1000 n [⟨.M, m⟩, ⟨.M, E - 2⟩] E = .newRound ms' W' ∧
      steps k (roundStart [⟨.M, m⟩, ⟨.M, E - 2⟩] E) = some (roundStart ms' W') ∧
      ((routeTreeEC Γ d).cutMem [(m : Int) / 2, ((E : Int) - 1) / 2] = true ∨ (0 < n ∧ cleanTape ms' W') ∨
        EntryNoCloseC ms' W') := by
  obtain ⟨hy, hs, hW, hwf⟩ := rtStart_point Γ m E hΓ hm hE h1 h2
  obtain ⟨n, k, ms', W', h1', h2', h3'⟩ :=
    RTree.soundE Γ 1000 (entryOKC Γ) EntryNoCloseC
      (fun _ _ _ _ _ _ h hlen hy hs hW => entryOKC_sound h hlen hy hs hW)
      (routeTreeEC Γ d) false _ _ _ (route_tree_entryC_ok Γ d) _ rfl hy _ _ hs hW hwf
  refine ⟨n, k, ms', W', h1', h2', ?_⟩
  rcases h3' with h | ⟨h, hc⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨by simpa using h, hc⟩)
  · exact Or.inr (Or.inr h)

/-- The clean-tape tree with loop entries that cannot close in a class of `closeClassC`, to depth `d` over the clean
tapes of width W ≥ Γ: `cleanTreeGE` with `cleanEntryOKC`. -/
def cleanTreeGEC (Γ d : Nat) : RTree :=
  RTree.exploreWE Γ 1000 (cleanEntryOKC Γ) cleanDrops (10000 + d) d cleanDrops false ctStart.1 ctStart.2.1
    ctStart.2.1 ctStart.2.2

theorem clean_tree_entryC_ok (Γ d : Nat) :
    (cleanTreeGEC Γ d).okWE Γ 1000 (cleanEntryOKC Γ) false ctStart.1 ctStart.2.1 ctStart.2.1 ctStart.2.2 = true :=
  RTree.exploreWE_okWE _ _ _ _ _ _ _ _ _ _ _ _

/-- **From a clean tape of width at least Γ, the machine reaches a wider clean tape or a loop entry that cannot close
in a class of `closeClassC`, unless W/2 is in a cut class.**  `clean_tree_entry_step` with `cleanTreeGEC`: for every
Γ ≥ 6, every depth d and every even W ≥ Γ, the machine started from the round start G 1, M W − 2 (width W) runs n
rounds of the mark model to a round start without halting, and either n ≥ 1 and that round start is a one-marker clean
tape of width W′ > W, or it is a phase-0 pass start of width W′ > W from which the loop cannot close in a class of
`closeClassC` (`EntryNoCloseC`), or W/2 lies in one of the cut classes of `cleanTreeGEC Γ d`. -/
theorem clean_tree_entry_stepC (Γ d W : Nat) (hΓ : 6 ≤ Γ) (hW : W % 2 = 0) (h : Γ ≤ W) :
    ∃ n k ms' W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound ms' W' ∧
      steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧
      ((cleanTreeGEC Γ d).cutMem [(W : Int) / 2, 0] = true ∨ (0 < n ∧ ms' = [⟨.M, W' - 2⟩] ∧ W < W') ∨
        (EntryNoCloseC ms' W' ∧ W < W')) := by
  let y : List Int := [(W : Int) / 2, 0]
  have hy : inCone ctStart.2.2 Γ y := by
    intro t ht
    simp only [ctStart, List.mem_cons, List.mem_nil_iff, or_false] at ht
    subst ht
    simp only [y, YForm.eval, dot]
    omega
  have hs : agL y ctStart.1 [⟨.M, W - 2⟩] := by
    refine ⟨⟨rfl, ?_⟩, trivial⟩
    simp only [agN, y, YForm.eval, YForm.addc, dot]
    omega
  have hW' : agN y ctStart.2.1 W := by simp only [agN, y, ctStart, YForm.eval, dot]; omega
  have hwf : roundWF [⟨.M, W - 2⟩] W := roundWF_one.mpr ⟨by omega, hW⟩
  obtain ⟨n, k, ms', W', h1', h2', h3'⟩ :=
    RTree.soundWE Γ 1000 (cleanEntryOKC Γ) (fun ms Wn W0 => EntryNoCloseC ms Wn ∧ W0 < Wn)
      (fun _ _ _ _ _ _ _ _ h hlen hy hs hW h0 => cleanEntryOKC_sound h hlen hy hs hW h0)
      (cleanTreeGEC Γ d) false _ _ _ _ (clean_tree_entryC_ok Γ d) y rfl hy _ _ _ hs hW' hW' hwf
  refine ⟨n, k, ms', W', h1', h2', ?_⟩
  rcases h3' with h | ⟨h, hc⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨by simpa using h, hc⟩)
  · exact Or.inr (Or.inr h)

/-! ## From a loop entry that cannot close -/

/-- Each class of `closeClassC` is in the table `closeTableC`. -/
theorem closeClassC_mem {R : Nat} {m c : Int} (h : closeClassC R = some (m, c)) : (R, m, c) ∈ closeTableC := by
  rcases closeClassC_closing h with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show closeClassC 2 = some (2, 0) from rfl] at h; cases h; simp [closeTableC]
  · rw [show closeClassC 4 = some (2, 0) from rfl] at h; cases h; simp [closeTableC]
  · rw [show closeClassC 8 = some (32, 0) from rfl] at h; cases h; simp [closeTableC]
  · rw [show closeClassC 16 = some (64, 0) from rfl] at h; cases h; simp [closeTableC]
  · rw [show closeClassC 32 = some (128, 0) from rfl] at h; cases h; simp [closeTableC]
  · rw [show closeClassC 48 = some (128, 0) from rfl] at h; cases h; simp [closeTableC]

/-- **A loop entry that cannot close in a class of `closeClassC` reaches none.**  The loop's chain from a pass start
of `EntryNoCloseC` never ends in a class of `closeClassC`: from a width at least 2²⁰ such a chain is p full passes,
after at most one half pass (`LoopChain.close_wideC`), and `EntryNoCloseC` excludes both. -/
theorem BB6.Sym.EntryNoCloseC.no_close {ms : List Mark} {W : Nat} (h : EntryNoCloseC ms W) {R : Nat}
    {ks : List StepKind} {ms₁ : List Mark} {W₁ R₁ : Nat} (hch : LoopChain ms W R ks ms₁ W₁ R₁)
    (hc : InCloseClassC ms₁ W₁ R₁) : False := by
  obtain ⟨hW, R', a, b, rfl, hP', -, hfull, hhalf⟩ := h
  -- the chain's right end is the entry's: both are the distance of the last wall from the end
  have hR : R = R' := by
    obtain ⟨a₂, b₂, e₂, -, -, -, -, -, -, -, h₂⟩ := hch.start
    obtain ⟨a₃, b₃, e₃, -, -, -, -, -, -, -, h₃⟩ := hP'
    simp only [List.cons.injEq, Mark.mk.injEq, true_and, and_true] at e₂ e₃
    omega
  subst hR
  obtain ⟨p, hp⟩ := hch.close_wideC hc (Nat.le_trans (Nat.pow_le_pow_right (by decide) (by decide)) hW)
  obtain ⟨a₁, b₁, m, c, rfl, hcc, hl⟩ := hc
  have hmem := closeClassC_mem hcc
  have h7 : passL1 [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁ % 7 = 3 := loopL1_mod7 _ _ _
  have hlm : passL1 [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁ % m = c := hl
  rcases hp with ⟨-, hR, hL⟩ | ⟨-, hW4, hR, hL⟩
  · exact hfull p R₁ m c _ hmem (by rw [hR]; push_cast; rfl) hL hlm h7
  · exact hhalf hW4 _ _ (by rw [hR]; push_cast; rw [Int.mul_assoc]) (by rw [← hL, Int.mul_assoc]) p R₁ m c _
      hmem rfl rfl hlm h7

/-- **From a loop entry that cannot close in a class of `closeClassC`, a halt needs the loop's chain to end first.**
`entry_halt` with `EntryNoCloseC` and `loop_halt_leaves_close`: if the machine halts from a pass start of
`EntryNoCloseC` (every gap at least 448, width at least 2²⁴, the middle wall at least 896 below the width when
W ≡ 2 mod 4, and no close in a class of `closeClassC` after full passes or after a half pass and full passes), then the
loop's chain from there (`LoopChain`) reaches no closing class: it ends, close-free, where the run, with every end
meeting at distance at least 2, has left phase 0 or the halving chain at a round start that is not three walls, and the
mark model reaches a stuck configuration after that. -/
theorem entry_halt_close {ms : List Mark} {W : Nat} (h : EntryNoCloseC ms W) (T : Nat)
    (hT : steps T (roundStart ms W) = none) :
    ∃ R ks ms₁ W₁ R₁, PassStart448 ms W R ∧ LoopChain ms W R ks ms₁ W₁ R₁ ∧
      ∃ n ms' W', roundsZ 1000 n ms₁ W₁ = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n ms₁ W₁, 2 ≤ d) ∧
        (LeftPhase0 n ms' ∨ ChainBreak (meetsRounds 1000 n ms₁ W₁)) ∧ NotWWW ms' ∧
        ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t) := by
  obtain ⟨hW, R, a, b, rfl, hP, hh, -⟩ := id h
  obtain ⟨ks, ms₁, W₁, R₁, hch, ⟨hc, -⟩ | he⟩ :=
    loop_halt_leaves_close R a b W hP (Nat.le_trans (Nat.pow_le_pow_right (by decide) (by decide)) hW) hh T hT
  · exact (h.no_close hch hc).elim
  · exact ⟨R, ks, ms₁, W₁, R₁, hP, hch, he⟩

/-- **A halt from a two-marker state with wide gaps does not close the loop where the route enters it, with the
narrower closing classes.**  `route_halt` with `routeTreeEC` and `entry_halt_close`: for every Γ ≥ 8, every depth d,
and all naturals m, E with m even, E odd and both gaps at least Γ, if the machine halts T steps after the round start
G 1, M m, M E − 2 (width E), then either (m/2, (E − 1)/2) lies in a cut class of `routeTreeEC Γ d`, or the machine runs
n rounds of the mark model (k steps) to a round start from which it halts, and that round start is a clean tape reached
after at least one round, or a phase-0 pass start with every gap at least 448 and width at least 2²⁴ from which the
loop's chain ends without a close, where the run, with every end meeting of the chain's last stretch at distance at
least 2, leaves three walls, and the halt needs a stuck configuration after that. -/
theorem route_halt_close (Γ d m E : Nat) (hΓ : 8 ≤ Γ) (hm : m % 2 = 0) (hE : E % 2 = 1) (h1 : Γ ≤ m)
    (h2 : m + Γ ≤ E) (T : Nat) (hT : steps T (roundStart [⟨.M, m⟩, ⟨.M, E - 2⟩] E) = none) :
    (routeTreeEC Γ d).cutMem [(m : Int) / 2, ((E : Int) - 1) / 2] = true ∨
    ∃ n k ms' W', roundsZ 1000 n [⟨.M, m⟩, ⟨.M, E - 2⟩] E = .newRound ms' W' ∧
      steps k (roundStart [⟨.M, m⟩, ⟨.M, E - 2⟩] E) = some (roundStart ms' W') ∧
      steps (T - k) (roundStart ms' W') = none ∧
      ((0 < n ∧ cleanTape ms' W') ∨
        ∃ R ks ms₁ W₁ R₁, PassStart448 ms' W' R ∧ 2 ^ 24 ≤ W' ∧ LoopChain ms' W' R ks ms₁ W₁ R₁ ∧
          ∃ n₂ ms'' W'', roundsZ 1000 n₂ ms₁ W₁ = .newRound ms'' W'' ∧ (∀ d ∈ meetsRounds 1000 n₂ ms₁ W₁, 2 ≤ d) ∧
            (LeftPhase0 n₂ ms'' ∨ ChainBreak (meetsRounds 1000 n₂ ms₁ W₁)) ∧ NotWWW ms'' ∧
            ∃ t, Reach ⟨[], 1, ms'', W''⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) := by
  obtain ⟨n, k, ms', W', h1', h2', h3'⟩ := route_tree_entryC Γ d m E hΓ hm hE h1 h2
  rcases h3' with hc | hc | hc
  · exact Or.inl hc
  · obtain ⟨-, hT'⟩ := steps_none_split hT h2'
    exact Or.inr ⟨n, k, ms', W', h1', h2', hT', Or.inl hc⟩
  · obtain ⟨-, hT'⟩ := steps_none_split hT h2'
    obtain ⟨R, ks, ms₁, W₁, R₁, hP, hch, he⟩ := entry_halt_close hc _ hT'
    exact Or.inr ⟨n, k, ms', W', h1', h2', hT', Or.inr ⟨R, ks, ms₁, W₁, R₁, hP, hc.1, hch, he⟩⟩

/-- **The routes, from blank tape, with the narrower closing classes.**  `blank_halt_route` with `routeTreeEC`: if the
machine, started on blank tape, halts after T steps, then at every two-marker state G 1, M m, M E − 2 (width E) that it
passes on its way with both gaps at least Γ ≥ 8, either (m/2, (E − 1)/2) lies in a cut class of `routeTreeEC Γ d` at
every depth d, or the machine runs n rounds of the mark model from there to a round start from which it halts, and that
round start is the next clean tape, or a loop entry (a phase-0 pass start with every gap at least 448 and width at least
2²⁴) from which the loop's chain ends without a close, where the run leaves three walls, and the halt needs a stuck
configuration after that. -/
theorem blank_halt_route_close (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∀ (Γ m E k : Nat), 8 ≤ Γ → m % 2 = 0 → E % 2 = 1 → Γ ≤ m → m + Γ ≤ E →
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, m⟩, ⟨.M, E - 2⟩] E) →
      (∀ d, (routeTreeEC Γ d).cutMem [(m : Int) / 2, ((E : Int) - 1) / 2] = true) ∨
      ∃ n k' ms' W', roundsZ 1000 n [⟨.M, m⟩, ⟨.M, E - 2⟩] E = .newRound ms' W' ∧
        steps k' (roundStart [⟨.M, m⟩, ⟨.M, E - 2⟩] E) = some (roundStart ms' W') ∧
        steps (T - k - k') (roundStart ms' W') = none ∧
        ((0 < n ∧ cleanTape ms' W') ∨
          ∃ R ks ms₁ W₁ R₁, PassStart448 ms' W' R ∧ 2 ^ 24 ≤ W' ∧ LoopChain ms' W' R ks ms₁ W₁ R₁ ∧
            ∃ n₂ ms'' W'', roundsZ 1000 n₂ ms₁ W₁ = .newRound ms'' W'' ∧ (∀ d ∈ meetsRounds 1000 n₂ ms₁ W₁, 2 ≤ d) ∧
              (LeftPhase0 n₂ ms'' ∨ ChainBreak (meetsRounds 1000 n₂ ms₁ W₁)) ∧ NotWWW ms'' ∧
              ∃ t, Reach ⟨[], 1, ms'', W''⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) := by
  intro Γ m E k hΓ hm hE h1 h2 hk
  obtain ⟨-, hT'⟩ := steps_none_split hT hk
  by_cases hall : ∀ d, (routeTreeEC Γ d).cutMem [(m : Int) / 2, ((E : Int) - 1) / 2] = true
  · exact Or.inl hall
  · obtain ⟨d, hd⟩ := Classical.not_forall.mp hall
    rcases route_halt_close Γ d m E hΓ hm hE h1 h2 (T - k) hT' with hc | h
    · exact absurd hc hd
    · exact Or.inr h

#print axioms route_tree_entryC
#print axioms clean_tree_entry_stepC
#print axioms BB6.Sym.EntryNoCloseC.no_close
#print axioms entry_halt_close
#print axioms route_halt_close
#print axioms blank_halt_route_close
