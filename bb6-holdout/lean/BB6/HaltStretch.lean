import BB6.HaltClose

/-!
# Closes at the right end, and halts after a covered stretch

Two additions to `HaltClose.lean`.

**Every contact at the right end is a close.**  `EndClose t`: the gap faces only the last mark, and either that mark
is the end marker at distance 0 with a mark touching the gap from the left (an end meeting at d = 0, `meetsOf = [0]`),
or it is a block touching the gap (the gap's last cell is then at most a few cells from the width: the block's three
cells and an even stripe).  `InteriorContact t`: a gap-phase contact with at least two marks to the right of the gap,
or a contact the packet meets on the left.  `stuck_cases`: every stuck configuration is one or the other, and
`halt_needs_end_close` is the sharpened conditional form of `halt_needs_close`: if no interior contact is reachable,
a halt needs a close at the right end.

**A halt from the start of a covered stretch needs a contact after the stretch.**  The model's rounds are runs of
`Step` (`roundZ_reach`, `roundsZ_reach`), `Step` keeps well-formedness and the invariants (`reach_inv`), and so
`halt_after_rounds`: if `roundsZ fuel n ms W = .newRound ms' W'` (the shape the certified stretches give, e.g.
`Tree.sound`, `Tree.soundNC`, `exit_no_halt`) and the machine halts from `roundStart ms W`, then it halts from
`roundStart ms' W'`, and the model, run on from that round start, reaches a stuck configuration.  Chaining stretches
this way, a halt needs an interior contact or a close at the right end after the last certified stretch.
-/

namespace BB6

/-! ## Contacts at the right end, and the others -/

/-- The gap faces only the last mark, and touches it: the end marker at distance 0 with a mark touching the gap from
the left, or a block. -/
def EndClose (t : GS) : Prop :=
  (t.msR = [⟨.M, t.g + 3⟩] ∧ touchesL t.g t.msL) ∨ t.msR = [⟨.B, t.g + 3⟩]

/-- A contact away from the right end: in the gap phase with at least two marks to the right of the gap, or met by
the packet on the left. -/
def InteriorContact (t : GS) : Prop :=
  (GapContact t.msL t.g t.msR ∧ 2 ≤ t.msR.length) ∨
  (∃ a x c d, t.ev = .pkt a x c d ∧ BackContact a) ∨
  (∃ a y c d, t.ev = .pktM a y c d ∧ LandContact a y)

/-- The end-marker case of `EndClose` is a close: an end meeting at distance 0. -/
theorem endClose_marker_close {t : GS} (h : t.msR = [⟨.M, t.g + 3⟩]) : Close t :=
  ⟨0, by rw [h]; exact swap0_end_close t.g, Nat.zero_le _⟩

theorem stuck_cases {t : GS} (h : Stuck t) : EndClose t ∨ InteriorContact t := by
  cases h with
  | gap hc =>
    generalize hm : t.msR = msR at hc
    cases hc with
    | swap0 r ht =>
      cases r with
      | nil => exact Or.inl (Or.inl ⟨hm, ht⟩)
      | cons m r =>
        refine Or.inr (Or.inl ⟨?_, ?_⟩)
        · rw [hm]; exact GapContact.swap0 _ _ _ ht
        · rw [hm]; simp
    | blockAtGap r =>
      cases r with
      | nil => exact Or.inl (Or.inr hm)
      | cons m r =>
        refine Or.inr (Or.inl ⟨?_, ?_⟩)
        · rw [hm]; exact GapContact.blockAtGap _ _ _
        · rw [hm]; simp
    | shift m₁ m₂ r h₁ h₂ =>
      refine Or.inr (Or.inl ⟨?_, ?_⟩)
      · rw [hm]; exact GapContact.shift _ _ _ _ _ h₁ h₂
      · rw [hm]; simp
  | pkt h hc => exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, h, hc⟩))
  | pktM h hc => exact Or.inr (Or.inr (Or.inr ⟨_, _, _, _, h, hc⟩))

/-- **A halt needs a close at the right end, unless an interior contact comes first.**  If no configuration the
model reaches from a well-formed start has an interior contact, a halt of the machine needs a configuration where the
gap touches the last mark: the d = 0 end meeting (a close) or a block. -/
theorem halt_needs_end_close (s : GS) (hwf : s.wf) (hB : noB s.msL) (hG : noG s.msR)
    (hint : ∀ t, Reach s t → t.wf → ¬ InteriorContact t) (T : Nat) (hT : steps T s.cfg = none) :
    ∃ t, Reach s t ∧ t.wf ∧ EndClose t := by
  obtain ⟨t, hr, hw, hs⟩ := halt_needs_contact T s hwf hB hG hT
  rcases stuck_cases hs with h | h
  · exact ⟨t, hr, hw, h⟩
  · exact absurd h (hint t hr hw)

/-- The same from blank tape. -/
theorem blank_halt_needs_end_close (hint : ∀ t, Reach ⟨[], 1, [], 5⟩ t → t.wf → ¬ InteriorContact t) (T : Nat)
    (hT : steps T ⟨blank, blank, .A⟩ = none) : ∃ t, Reach ⟨[], 1, [], 5⟩ t ∧ t.wf ∧ EndClose t := by
  obtain ⟨-, hT'⟩ := steps_none_split hT first_round_start
  exact halt_needs_end_close ⟨[], 1, [], 5⟩ ⟨⟨fun _ => rfl, fun _ => rfl⟩, Or.inl first_round_start_wf⟩
    (fun _ h => absurd h List.not_mem_nil) noG_nil hint _ hT'

/-! ## Rounds are runs of `Step` -/

theorem Reach.trans {s t u : GS} (h₁ : Reach s t) (h₂ : Reach t u) : Reach s u := by
  induction h₁ with
  | refl => exact h₂
  | head hs _ ih => exact Reach.head hs (ih h₂)

theorem roundZ_reach (fuel : Nat) : ∀ (msL : List Mark) (g : Nat) (msR : List Mark) (W : Nat) (ms' : List Mark)
    (W' : Nat), roundZ fuel msL g msR W = .newRound ms' W' → Reach ⟨msL, g, msR, W⟩ ⟨[], 1, ms', W'⟩ := by
  induction fuel with
  | zero => intro _ _ _ _ _ _ h; cases h
  | succ fuel ih =>
    intro msL g msR W ms' W' h
    simp only [roundZ] at h
    have hev : GS.ev ⟨msL, g, msR, W⟩ = gapEvent msL g msR W := rfl
    generalize gapEvent msL g msR W = r at h hev
    cases r with
    | gap a b c d => exact Reach.head (Step.gap hev) (ih a b c d ms' W' h)
    | pkt a x c d =>
      dsimp only at h
      cases hp : pktBack a x c d with
      | gap a' b' c' d' =>
        rw [hp] at h
        have hn : (pktBack a x c d).next = some ⟨a', b', c', d'⟩ := by rw [hp]; rfl
        exact Reach.head (Step.pkt hev hn) (ih a' b' c' d' ms' W' h)
      | newRound ms₁ W₁ =>
        rw [hp] at h
        simp only [PR'.cont, PR'.newRound.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hn : (pktBack a x c d).next = some ⟨[], 1, ms₁, W₁⟩ := by rw [hp]; rfl
        exact Reach.head (Step.pkt hev hn) (Reach.refl _)
      | halt => rw [hp] at h; cases h
      | uncovered => rw [hp] at h; cases h
    | pktM a y c d =>
      dsimp only at h
      cases hp : pktLand a y c d with
      | gap a' b' c' d' =>
        rw [hp] at h
        have hn : (pktLand a y c d).next = some ⟨a', b', c', d'⟩ := by rw [hp]; rfl
        exact Reach.head (Step.pktM hev hn) (ih a' b' c' d' ms' W' h)
      | newRound ms₁ W₁ =>
        rw [hp] at h
        simp only [PR'.cont, PR'.newRound.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hn : (pktLand a y c d).next = some ⟨[], 1, ms₁, W₁⟩ := by rw [hp]; rfl
        exact Reach.head (Step.pktM hev hn) (Reach.refl _)
      | halt => rw [hp] at h; cases h
      | uncovered => rw [hp] at h; cases h
    | halt => cases h
    | uncovered => cases h

theorem roundsZ_reach (fuel n : Nat) : ∀ (ms : List Mark) (W : Nat) (ms' : List Mark) (W' : Nat),
    roundsZ fuel n ms W = .newRound ms' W' → Reach ⟨[], 1, ms, W⟩ ⟨[], 1, ms', W'⟩ := by
  induction n with
  | zero =>
    intro ms W ms' W' h
    simp only [roundsZ, PR'.newRound.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Reach.refl _
  | succ n ih =>
    intro ms W ms' W' h
    simp only [roundsZ] at h
    cases hr : roundZ fuel [] 1 ms W with
    | newRound ms₁ W₁ =>
      rw [hr] at h
      exact Reach.trans (roundZ_reach fuel [] 1 ms W ms₁ W₁ hr) (ih ms₁ W₁ ms' W' h)
    | gap _ _ _ _ => rw [hr] at h; cases h
    | halt => rw [hr] at h; cases h
    | uncovered => rw [hr] at h; cases h

/-! ## The invariants along the run -/

theorem step_inv {s t : GS} (h : Step s t) (hwf : s.wf) (hB : noB s.msL) (hG : noG s.msR) :
    t.wf ∧ noB t.msL ∧ noG t.msR := by
  have hinv := gapEvent_inv s.msL s.g s.msR s.W hwf hB hG
  have hok := gapEvent_ok s.msL s.g s.msR s.W hwf
  cases h with
  | gap he =>
    rw [show gapEvent s.msL s.g s.msR s.W = _ from he] at hinv hok
    exact ⟨hok.2, hinv.1, hinv.2.1⟩
  | @pkt _ a x c d he hn =>
    rw [show gapEvent s.msL s.g s.msR s.W = _ from he] at hinv hok
    obtain ⟨-, hL, hR⟩ := hok
    have hpi := pktBack_inv a x c d hL hinv.1 hinv.2
    exact ⟨gapWF_of_wf (pktBack_wf a x c d hL hR) hn, inv_of_next hpi hn⟩
  | @pktM _ a y c d he hn =>
    rw [show gapEvent s.msL s.g s.msR s.W = _ from he] at hinv hok
    obtain ⟨-, hL, hR⟩ := hok
    have hpi := pktLand_inv a y c d hL hinv.1 hinv.2
    exact ⟨gapWF_of_wf (pktLand_wf a y c d hL hR) hn, inv_of_next hpi hn⟩

theorem reach_inv {s t : GS} (h : Reach s t) (hwf : s.wf) (hB : noB s.msL) (hG : noG s.msR) :
    t.wf ∧ noB t.msL ∧ noG t.msR := by
  induction h with
  | refl => exact ⟨hwf, hB, hG⟩
  | head hs _ ih =>
    obtain ⟨h1, h2, h3⟩ := step_inv hs hwf hB hG
    exact ih h1 h2 h3

/-! ## Halts after a covered stretch -/

/-- **A halt from the start of a covered stretch needs a contact after it.**  If the model covers `n` rounds from a
well-formed round start without sleeping gaps, ending at the round start `ms' W'`, and the machine halts from the
first round start, then it reaches `roundStart ms' W'` first, halts from there, and the model, run on from `ms' W'`,
reaches a stuck configuration (on the same model run as the stretch). -/
theorem halt_after_rounds (fuel n : Nat) (ms : List Mark) (W : Nat) (ms' : List Mark) (W' : Nat)
    (h : roundWF ms W) (hG : noG ms) (hr : roundsZ fuel n ms W = .newRound ms' W') (T : Nat)
    (hT : steps T (roundStart ms W) = none) :
    ∃ k, k ≤ T ∧ steps k (roundStart ms W) = some (roundStart ms' W') ∧ steps (T - k) (roundStart ms' W') = none ∧
      Reach ⟨[], 1, ms, W⟩ ⟨[], 1, ms', W'⟩ ∧
      ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ Stuck t := by
  have hs : GS.wf ⟨[], 1, ms, W⟩ := ⟨⟨fun _ => rfl, fun _ => rfl⟩, Or.inl h⟩
  have hB : noB ([] : List Mark) := fun _ h => absurd h List.not_mem_nil
  have hreach := roundsZ_reach fuel n ms W ms' W' hr
  obtain ⟨hwf', hB', hG'⟩ := reach_inv hreach hs hB hG
  obtain ⟨k, hk, -⟩ := rounds_run fuel n ms W h (by rw [hr]; intro h; cases h)
  rw [hr] at hk
  obtain ⟨hle, hT'⟩ := steps_none_split hT hk
  exact ⟨k, hle, hk, hT', hreach, halt_needs_contact (T - k) _ hwf' hB' hG' hT'⟩

end BB6
