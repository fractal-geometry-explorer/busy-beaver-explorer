import BB6.HaltStretch
import BB6.BlockHalt

/-!
# A close at the right end is a halt

`halt_needs_end_close` (`HaltStretch.lean`) goes one way: if the machine halts and no interior contact is reachable,
the mark model reaches a close at the right end (`EndClose`).  This file goes the other way for the close that every
sampled halt goes through: the gap meets the end marker at distance 0, a marker touches the gap from the left, and the
end marker is the last thing on the tape (`EndClose0`).  From there the machine halts 54 steps later, without reading
the tape left of the touching marker (`end_close_local`), and every step of the model is a run of the machine
(`Step.run`, `Reach.run`), so if the model reaches such a configuration from a well-formed start, the machine halts
(`reach_close_halt`).  With both directions, `halt_iff_end_close`: when no interior contact is reachable and every
close at the right end is of this kind, the machine halts exactly when the model reaches one.

`closeRun` runs the model event by event and reports whether it reaches such a close; `closeRun_sound` makes that a
proof that the machine halts, for a concrete start (`decide +kernel`).  `symCloseRun` does the same on symbolic
positions, for a whole class of round starts (a cone of points, as in the endgame trees), and `symCloseRun_halt` makes
its success a proof that every member of the class halts.
-/

namespace BB6

/-! ## The model's steps are runs of the machine -/

/-- One step of the model (a gap event, or a gap event and the packet phase it starts) is a run of the machine. -/
theorem Step.run {s t : GS} (h : Step s t) (hwf : s.wf) : ∃ n, steps n s.cfg = some t.cfg := by
  have hok := gapEvent_ok s.msL s.g s.msR s.W hwf
  cases h with
  | gap he =>
    rw [show gapEvent s.msL s.g s.msR s.W = _ from he] at hok
    exact hok.1
  | @pkt _ a x c d he hn =>
    rw [show gapEvent s.msL s.g s.msR s.W = _ from he] at hok
    obtain ⟨⟨n₁, h₁⟩, hL, hR⟩ := hok
    have hnu : pktBack a x c d ≠ .uncovered := by intro h; rw [h] at hn; cases hn
    obtain ⟨n₂, h₂⟩ := pktBack_run a x c d hL hR hnu
    rw [cfg_of_next hn] at h₂
    exact ⟨n₁ + n₂, steps_seq h₁ h₂⟩
  | @pktM _ a y c d he hn =>
    rw [show gapEvent s.msL s.g s.msR s.W = _ from he] at hok
    obtain ⟨⟨n₁, h₁⟩, hL, hR⟩ := hok
    have hnu : pktLand a y c d ≠ .uncovered := by intro h; rw [h] at hn; cases hn
    obtain ⟨n₂, h₂⟩ := pktLand_run a y c d hL hR hnu
    rw [cfg_of_next hn] at h₂
    exact ⟨n₁ + n₂, steps_seq h₁ h₂⟩

/-- Everything the model reaches from a well-formed start, the machine reaches. -/
theorem Reach.run {s t : GS} (h : Reach s t) (hwf : s.wf) (hB : noB s.msL) (hG : noG s.msR) :
    ∃ n, steps n s.cfg = some t.cfg := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | head hs _ ih =>
    obtain ⟨n₁, h₁⟩ := Step.run hs hwf
    obtain ⟨hw, hb, hg⟩ := step_inv hs hwf hB hG
    obtain ⟨n₂, h₂⟩ := ih hw hb hg
    exact ⟨n₁ + n₂, steps_seq h₁ h₂⟩

/-! ## The close, on the machine -/

/-- The close at the right end that the sampled halts go through: the end marker at distance 0 from the gap, a
marker touching the gap from the left, and nothing after the end marker (W = g + 5). -/
def EndClose0 (t : GS) : Prop := t.msR = [⟨.M, t.g + 3⟩] ∧ touchesL t.g t.msL ∧ t.W = t.g + 5

theorem EndClose0.endClose {t : GS} (h : EndClose0 t) : EndClose t := Or.inl ⟨h.1, h.2.1⟩

/-- **The 54 steps of the close.**  The touching marker `11`, the gap `000` with the head on its last cell in state E,
the end marker `11`, blank tape: the machine halts on the touching marker's first cell after 54 steps, whatever lies
further left. -/
theorem end_close_local (L : Tape) :
    steps 55 ⟨cons false (cons false (cons true (cons true L))), cons false (cons true (cons true blank)), .E⟩ = none :=
  rfl

theorem endClose0_cfg {t : GS} (hwf : t.wf) (hB : noB t.msL) (h : EndClose0 t) :
    ∃ L, t.cfg = ⟨cons false (cons false (cons true (cons true L))), cons false (cons true (cons true blank)), .E⟩ := by
  obtain ⟨msL, g, msR, W⟩ := t
  obtain ⟨hR, ht, hW⟩ := h
  simp only at hR ht hW
  subst hR hW
  cases msL with
  | nil => exact absurd ht id
  | cons m ms =>
    obtain ⟨tm, p⟩ := m
    simp only [touchesL] at ht
    have hpar := hwf.1.2.1
    simp only [ht, Nat.sub_self] at hpar
    cases tm with
    | M =>
      refine ⟨buildL true p ms, ?_⟩
      simp only [mlen] at ht
      have hp : g - (p + 2) = 0 := by omega
      simp only [GS.cfg, midCfg, buildL, build, mcells, mval, mlen, hp, Nat.sub_self, stripe_zero,
        Bool.not_false, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, app_cons, app_nil]
    | B => exact absurd rfl (noB_head hB)
    | G => simp [mval] at hpar
    | W => simp [mval] at hpar

/-- From the close the machine halts within 55 steps. -/
theorem endClose0_halt {t : GS} (hwf : t.wf) (hB : noB t.msL) (h : EndClose0 t) : steps 55 t.cfg = none := by
  obtain ⟨L, hL⟩ := endClose0_cfg hwf hB h
  rw [hL]
  exact end_close_local L

/-! ## A close the model reaches is a halt -/

/-- **A close that the model reaches is a halt.**  From a well-formed configuration with no block on its left and no
sleeping gap on its right, if the model reaches the close `EndClose0` (over any number of events and rounds), the
machine halts. -/
theorem reach_close_halt {s t : GS} (hwf : s.wf) (hB : noB s.msL) (hG : noG s.msR) (hr : Reach s t)
    (h : EndClose0 t) : ∃ T, steps T s.cfg = none := by
  obtain ⟨n, hn⟩ := Reach.run hr hwf hB hG
  obtain ⟨htw, htB, -⟩ := reach_inv hr hwf hB hG
  exact ⟨n + 55, steps_seq_none hn (endClose0_halt htw htB h)⟩

/-- The same from a round start. -/
theorem round_close_halt (ms : List Mark) (W : Nat) (h : roundWF ms W) (hG : noG ms) {t : GS}
    (hr : Reach ⟨[], 1, ms, W⟩ t) (hc : EndClose0 t) : ∃ T, steps T (roundStart ms W) = none :=
  reach_close_halt (s := ⟨[], 1, ms, W⟩) ⟨⟨fun _ => rfl, fun _ => rfl⟩, Or.inl h⟩
    (fun _ h => absurd h List.not_mem_nil) hG hr hc

/-- **Halts are exactly the closes the model reaches**, when the model reaches no interior contact and every close at
the right end it reaches is of the kind above (both measured, neither proved): the machine halts from a well-formed
configuration if and only if the model reaches such a close. -/
theorem halt_iff_end_close (s : GS) (hwf : s.wf) (hB : noB s.msL) (hG : noG s.msR)
    (hint : ∀ t, Reach s t → t.wf → ¬ InteriorContact t) (h0 : ∀ t, Reach s t → t.wf → EndClose t → EndClose0 t) :
    (∃ T, steps T s.cfg = none) ↔ ∃ t, Reach s t ∧ EndClose0 t := by
  constructor
  · rintro ⟨T, hT⟩
    obtain ⟨t, hr, hw, he⟩ := halt_needs_end_close s hwf hB hG hint T hT
    exact ⟨t, hr, h0 t hr hw he⟩
  · rintro ⟨t, hr, ht⟩
    exact reach_close_halt hwf hB hG hr ht

/-! ## Running the model to a close -/

/-- `EndClose0`, as a test. -/
def endClose0B (s : GS) : Bool :=
  match s.msR, s.msL with
  | [⟨.M, p⟩], m :: _ => p == s.g + 3 && m.p + mlen m.t == s.g && s.W == s.g + 5
  | _, _ => false

theorem endClose0B_sound {s : GS} (h : endClose0B s = true) : EndClose0 s := by
  obtain ⟨msL, g, msR, W⟩ := s
  cases msR with
  | nil => simp [endClose0B] at h
  | cons m r =>
    cases r with
    | cons _ _ => simp [endClose0B] at h
    | nil =>
      obtain ⟨tm, p⟩ := m
      cases tm with
      | M =>
        cases msL with
        | nil => simp [endClose0B] at h
        | cons m ms =>
          simp only [endClose0B, Bool.and_eq_true, beq_iff_eq] at h
          obtain ⟨⟨hp, hm⟩, hW⟩ := h
          subst hp
          exact ⟨rfl, hm, hW⟩
      | G => simp [endClose0B] at h
      | W => simp [endClose0B] at h
      | B => simp [endClose0B] at h

/-- Run the model event by event from `s`, across rounds, for at most `fuel` events, and say whether it reaches the
close `EndClose0`. -/
def closeRun : Nat → GS → Bool
  | 0, _ => false
  | fuel + 1, s =>
    endClose0B s ||
    match gapEvent s.msL s.g s.msR s.W with
    | .gap a b c d => closeRun fuel ⟨a, b, c, d⟩
    | .pkt a x c d =>
      match (pktBack a x c d).next with
      | some t => closeRun fuel t
      | none => false
    | .pktM a y c d =>
      match (pktLand a y c d).next with
      | some t => closeRun fuel t
      | none => false
    | _ => false

theorem closeRun_reach : ∀ (fuel : Nat) (s : GS), closeRun fuel s = true → ∃ t, Reach s t ∧ EndClose0 t := by
  intro fuel
  induction fuel with
  | zero => intro s h; cases h
  | succ fuel ih =>
    intro s h
    simp only [closeRun, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨s, Reach.refl s, endClose0B_sound h⟩
    · have hev : s.ev = gapEvent s.msL s.g s.msR s.W := rfl
      generalize gapEvent s.msL s.g s.msR s.W = r at h hev
      cases r with
      | gap a b c d =>
        obtain ⟨t, ht, hc⟩ := ih _ h
        exact ⟨t, Reach.head (Step.gap hev) ht, hc⟩
      | pkt a x c d =>
        simp only at h
        split at h
        · rename_i t hn
          obtain ⟨u, hu, hc⟩ := ih _ h
          exact ⟨u, Reach.head (Step.pkt hev hn) hu, hc⟩
        · cases h
      | pktM a y c d =>
        simp only at h
        split at h
        · rename_i t hn
          obtain ⟨u, hu, hc⟩ := ih _ h
          exact ⟨u, Reach.head (Step.pktM hev hn) hu, hc⟩
        · cases h
      | halt => cases h
      | uncovered => cases h

/-- **A run of the model to a close proves a halt**, from a well-formed round start without sleeping gaps. -/
theorem closeRun_sound (fuel : Nat) (ms : List Mark) (W : Nat) (h : roundWF ms W) (hG : noG ms)
    (hc : closeRun fuel ⟨[], 1, ms, W⟩ = true) : ∃ T, steps T (roundStart ms W) = none := by
  obtain ⟨t, ht, he⟩ := closeRun_reach fuel _ hc
  exact round_close_halt ms W h hG ht he

/-! ## On a class: the close run on symbolic positions -/

namespace Sym

section
variable (ts : List YForm) (Γ : Int)

/-- `EndClose0`, decided on a class. -/
def symEndClose0 (sL : List SMark) (sg : YForm) (sR : List SMark) (sW : YForm) : Bool :=
  match sR, sL with
  | [⟨.M, p⟩], m :: _ =>
    eqDec p (sg.addc 3) ts Γ == some true && eqDec (m.p.addc (mlen m.t)) sg ts Γ == some true &&
      eqDec sW (sg.addc 5) ts Γ == some true
  | _, _ => false

theorem symEndClose0_sound {y : List Int} (hy : inCone ts Γ y) {sL : List SMark} {msL : List Mark} {sg : YForm}
    {g : Nat} {sR : List SMark} {msR : List Mark} {sW : YForm} {Wn : Nat} (hL : agL y sL msL) (hg : agN y sg g)
    (hR : agL y sR msR) (hW : agN y sW Wn) (h : symEndClose0 ts Γ sL sg sR sW = true) :
    EndClose0 ⟨msL, g, msR, Wn⟩ := by
  match sR, msR, sL, msL, hR, hL, h with
  | [⟨.M, p⟩], [m'], s :: _, m :: _, hR, hL, h =>
    simp only [symEndClose0, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨h₁, h₂⟩, h₃⟩ := h
    obtain ⟨⟨ht', hp'⟩, -⟩ := hR
    obtain ⟨⟨ht, hp⟩, -⟩ := hL
    have e₁ := (eq_of_eqDec hy hp' (agN_addc hg 3) h₁).mpr rfl
    have e₂ := (eq_of_eqDec hy (agN_addc hp (mlen s.t)) hg h₂).mpr rfl
    have e₃ := (eq_of_eqDec hy hW (agN_addc hg 5) h₃).mpr rfl
    obtain ⟨tm', p'⟩ := m'
    simp only at ht' e₁
    subst ht' e₁
    refine ⟨rfl, ?_, e₃⟩
    simp only [touchesL]
    rw [← ht]
    exact e₂
  | [], _, _, _, _, _, h => simp [symEndClose0] at h
  | [⟨.M, _⟩], [], _, _, hR, _, _ => exact absurd hR id
  | [⟨.M, _⟩], _ :: _ :: _, _, _, hR, _, _ => exact absurd hR.2 id
  | [⟨.M, _⟩], [_], [], _, _, _, h => simp [symEndClose0] at h
  | [⟨.M, _⟩], [_], _ :: _, [], _, hL, _ => exact absurd hL id
  | [⟨.G, _⟩], _, _, _, _, _, h => simp [symEndClose0] at h
  | [⟨.W, _⟩], _, _, _, _, _, h => simp [symEndClose0] at h
  | [⟨.B, _⟩], _, _, _, _, _, h => simp [symEndClose0] at h
  | _ :: _ :: _, _, _, _, _, _, h => simp [symEndClose0] at h

/-- `closeRun` on symbolic positions: run the model event by event on the class, across rounds, for at most `fuel`
events, and say whether every member reaches the close `EndClose0` (`false` also where a step is undecided). -/
def symCloseRun : Nat → List SMark → YForm → List SMark → YForm → Bool
  | 0, _, _, _, _ => false
  | fuel + 1, sL, sg, sR, sW =>
    symEndClose0 ts Γ sL sg sR sW ||
    match symGapEvent ts Γ sL sg sR sW with
    | some (.gap a b c d) => symCloseRun fuel a b c d
    | some (.pkt a x c d) =>
      match symPktBack ts Γ a x c d with
      | some (.gap a' b' c' d') => symCloseRun fuel a' b' c' d'
      | some (.newRound ms W) => symCloseRun fuel [] (YForm.const 1) ms W
      | _ => false
    | some (.pktM a x c d) =>
      match symPktLand ts Γ a x c d with
      | some (.gap a' b' c' d') => symCloseRun fuel a' b' c' d'
      | some (.newRound ms W) => symCloseRun fuel [] (YForm.const 1) ms W
      | _ => false
    | _ => false

/-- The next configuration after a packet phase that agrees with a symbolic gap configuration or round start. -/
theorem next_of_agPR {y : List Int} {pr : SPR} {cr : PR'} (h : agPR y pr cr) :
    (∀ a b c d, pr = .gap a b c d → ∃ a' b' c' d', cr.next = some ⟨a', b', c', d'⟩ ∧ agL y a a' ∧ agN y b b' ∧
      agL y c c' ∧ agN y d d') ∧
    (∀ ms W, pr = .newRound ms W → ∃ ms' W', cr.next = some ⟨[], 1, ms', W'⟩ ∧ agL y ms ms' ∧ agN y W W') := by
  constructor
  · intro a b c d hp
    subst hp
    cases cr with
    | gap a' b' c' d' => exact ⟨a', b', c', d', rfl, h.1, h.2.1, h.2.2.1, h.2.2.2⟩
    | _ => exact absurd h id
  · intro ms W hp
    subst hp
    cases cr with
    | newRound ms' W' => exact ⟨ms', W', rfl, h.1, h.2⟩
    | _ => exact absurd h id

theorem symCloseRun_sound {y : List Int} (hy : inCone ts Γ y) (fuel : Nat) :
    ∀ (sL : List SMark) (msL : List Mark) (sg : YForm) (g : Nat) (sR : List SMark) (msR : List Mark) (sW : YForm)
      (Wn : Nat), agL y sL msL → agN y sg g → agL y sR msR → agN y sW Wn → symCloseRun ts Γ fuel sL sg sR sW = true →
      ∃ t, Reach ⟨msL, g, msR, Wn⟩ t ∧ EndClose0 t := by
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ h; cases h
  | succ fuel ih =>
    intro sL msL sg g sR msR sW Wn hL hg hR hW h
    simp only [symCloseRun, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨_, Reach.refl _, symEndClose0_sound ts Γ hy hL hg hR hW h⟩
    · have hev : GS.ev ⟨msL, g, msR, Wn⟩ = gapEvent msL g msR Wn := rfl
      cases he : symGapEvent ts Γ sL sg sR sW with
      | none => rw [he] at h; cases h
      | some ev =>
        rw [he] at h
        have hag := symGapEvent_sound ts Γ hy hL hg hR hW he
        generalize gapEvent msL g msR Wn = cev at hag hev
        cases ev with
        | gap a b c d =>
          cases cev with
          | gap a' b' c' d' =>
            obtain ⟨t, ht, hc⟩ := ih _ _ _ _ _ _ _ _ hag.1 hag.2.1 hag.2.2.1 hag.2.2.2 h
            exact ⟨t, Reach.head (Step.gap hev) ht, hc⟩
          | _ => exact absurd hag id
        | pkt a x c d =>
          cases cev with
          | pkt a' x' c' d' =>
            simp only at h
            cases hb : symPktBack ts Γ a x c d with
            | none => rw [hb] at h; cases h
            | some pr =>
              rw [hb] at h
              have hpr := symPktBack_sound ts Γ hy a a' x x' c c' d d' pr hag.1 hag.2.2.1 hag.2.2.2 hb
              obtain ⟨hgap, hnew⟩ := next_of_agPR hpr
              cases pr with
              | gap a₁ b₁ c₁ d₁ =>
                obtain ⟨a₂, b₂, c₂, d₂, hn, h₁, h₂, h₃, h₄⟩ := hgap _ _ _ _ rfl
                obtain ⟨t, ht, hc⟩ := ih _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h
                exact ⟨t, Reach.head (Step.pkt hev hn) ht, hc⟩
              | newRound ms W =>
                obtain ⟨ms', W', hn, h₁, h₂⟩ := hnew _ _ rfl
                obtain ⟨t, ht, hc⟩ := ih [] [] (YForm.const 1) 1 _ _ _ _ trivial (agN_const y 1) h₁ h₂ h
                exact ⟨t, Reach.head (Step.pkt hev hn) ht, hc⟩
              | halt => cases h
              | uncovered => cases h
          | _ => exact absurd hag id
        | pktM a x c d =>
          cases cev with
          | pktM a' x' c' d' =>
            simp only at h
            cases hb : symPktLand ts Γ a x c d with
            | none => rw [hb] at h; cases h
            | some pr =>
              rw [hb] at h
              have hpr := symPktLand_sound ts Γ hy a a' x x' c c' d d' pr hag.1 hag.2.1 hag.2.2.1 hag.2.2.2 hb
              obtain ⟨hgap, hnew⟩ := next_of_agPR hpr
              cases pr with
              | gap a₁ b₁ c₁ d₁ =>
                obtain ⟨a₂, b₂, c₂, d₂, hn, h₁, h₂, h₃, h₄⟩ := hgap _ _ _ _ rfl
                obtain ⟨t, ht, hc⟩ := ih _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h
                exact ⟨t, Reach.head (Step.pktM hev hn) ht, hc⟩
              | newRound ms W =>
                obtain ⟨ms', W', hn, h₁, h₂⟩ := hnew _ _ rfl
                obtain ⟨t, ht, hc⟩ := ih [] [] (YForm.const 1) 1 _ _ _ _ trivial (agN_const y 1) h₁ h₂ h
                exact ⟨t, Reach.head (Step.pktM hev hn) ht, hc⟩
              | halt => cases h
              | uncovered => cases h
          | _ => exact absurd hag id
        | halt => cases h
        | uncovered => cases h

/-- **Halts on a whole class.**  If the close run on symbolic positions reaches the close from a round start, every
member of the class (a point of the cone agreeing with the marks and the width) halts, provided its round start is
well formed and has no sleeping gap. -/
theorem symCloseRun_halt (fuel : Nat) {ss : List SMark} {sW : YForm}
    (hc : symCloseRun ts Γ fuel [] (YForm.const 1) ss sW = true) {y : List Int} (hy : inCone ts Γ y) {ms : List Mark}
    {W : Nat} (hs : agL y ss ms) (hWa : agN y sW W) (hwf : roundWF ms W) (hG : noG ms) :
    ∃ T, steps T (roundStart ms W) = none := by
  obtain ⟨t, ht, he⟩ := symCloseRun_sound ts Γ hy fuel [] [] (YForm.const 1) 1 ss ms sW W trivial (agN_const y 1) hs
    hWa hc
  exact round_close_halt ms W hwf hG ht he

end

end Sym

end BB6
