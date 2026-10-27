import BB6.Loop

/-!
# Where a stretch from a pass start ends

The no-close trees certify a stretch of rounds without a close from each phase-0 pass start.  A statement about the
machine has to say where that stretch ends: "the run makes some number n of rounds without a close" holds with n = 0
for any start, so it carries nothing.  The ends, as facts about the mark model's run from a pass start of width E with
right end R and left countdown L:

* the run has left the loop, at a round start that is not three walls (`NotWWW`): it left phase 0 (`LeftPhase0 n ms`:
  after round 1 the marks are not B, W, or after round 2 not M, B), or its end meetings left the halving chain
  (`ChainBreak ds`: two consecutive ones at distances d, d′ with d′ ≠ d/2 + 4 for d ≡ 0 mod 4, d′ ≠ (d − 2)/2 for
  d ≡ 2 mod 4, or d odd);
* or the run is at a landing of the loop's chain (`Landing`): three walls with the phase-0 parities (a odd, b even,
  width W ≡ 0 mod 4), right end R′ even and at least 2, reached by one of three steps (`StepMap`): a full pass
  (8 rounds; R′ = R/16, L₁′ = L/64, W = E + 24), a half pass (2 rounds, from E ≡ 2 mod 4; R′ = R/2,
  L₁′ = (L + 35E − 147R − 60)/2, W = E + 6) or a break of the end-meeting chain at round 7
  (R′ = (476E + 980R − L + 15984)/4704, L₁′ = (L + 1120E + 1666R + 50328)/96, W = E + 24).

None of them holds after zero rounds: the start is three walls, and each step takes rounds.  A stretch from a loop
state (three walls, either phase: the exit) ends at an `ExitEvent`: a clean tape (`CleanTape`), a `ChainBreak`, or a
loop state again after a full pass of 8 rounds (`LoopReturn`); none of them holds after zero rounds either.
`Tree.okEnd` checks a tree as `Tree.okNC` does and, at each leaf, one of the ends of its kind (`EndSpec`); for a right
end in the closing set a leaf may instead show that the left countdown L₁ is in a given residue class.
`Tree.soundEnd` is the statement for the machine.
-/

namespace BB6
open BB6

/-- The end-meeting chain: after an end meeting at distance d the next one is at d/2 + 4 (d ≡ 0 mod 4) or at
(d − 2)/2 (d ≡ 2 mod 4); an odd distance has no successor. -/
def ChainNext (d d' : Nat) : Prop := (d % 4 = 0 ∧ d' = d / 2 + 4) ∨ (d % 4 = 2 ∧ d' = (d - 2) / 2)

/-- Two consecutive end meetings off the chain. -/
def ChainBreak (ds : List Nat) : Prop := ∃ l₁ d d' l₂, ds = l₁ ++ d :: d' :: l₂ ∧ ¬ ChainNext d d'

/-- After round 1 the marks are not B, W, or after round 2 not M, B: the run does not follow the loop's phase 0. -/
def LeftPhase0 (n : Nat) (ms : List Mark) : Prop :=
  (n = 1 ∧ ms.map Mark.t ≠ [.B, .W]) ∨ (n = 2 ∧ ms.map Mark.t ≠ [.M, .B])

/-- The left countdown L₁ = 147 b + 280 W − 392 c − 578 of a round start with three marks at a, b, c (`loopL1`; 0 for
any other round start). -/
def passL1 : List Mark → Nat → Int
  | [_, m₂, m₃], W => loopL1 m₂.p m₃.p W
  | _, _ => 0

/-- The kinds of step of the loop's chain, from a pass start to the next three-wall round start with the phase-0
parities: a full pass, a half pass, and a break of the end-meeting chain at round 7. -/
inductive StepKind
  | full
  | half
  | break7
  deriving DecidableEq, Repr

/-- The map of a step of kind `k`, after `n` rounds from a pass start of width E with right end R and left countdown
L, to a round start of width W with right end R′ and left countdown L′.  A full pass takes 8 rounds, R′ = R/16,
L′ = L/64 and W = E + 24; a half pass 2 rounds, from E ≡ 2 (mod 4), R′ = R/2, L′ = (L + 35E − 147R − 60)/2 and
W = E + 6; a break of the chain at round 7 has 4704 R′ = 476E + 980R − L + 15984, 96 L′ = L + 1120E + 1666R + 50328
and W = E + 24. -/
def StepMap : StepKind → Nat → Nat → Nat → Int → Nat → Nat → Int → Prop
  | .full, n, E, R, L, W, R', L' => n = 8 ∧ 16 * R' = R ∧ 64 * L' = L ∧ W = E + 24
  | .half, n, E, R, L, W, R', L' =>
    n = 2 ∧ 2 * R' = R ∧ 2 * L' = L + 35 * (E : Int) - 147 * (R : Int) - 60 ∧ W = E + 6 ∧ E % 4 = 2
  | .break7, n, E, R, L, W, R', L' =>
    n = 7 ∧ 4704 * (R' : Int) = 476 * (E : Int) + 980 * (R : Int) - L + 15984 ∧
      96 * L' = L + 1120 * (E : Int) + 1666 * (R : Int) + 50328 ∧ W = E + 24

/-- A landing of the loop's chain, after `n` rounds from a pass start of width E with right end R and left countdown
L: three walls at a, b, c with the phase-0 parities (a odd, b even, W ≡ 0 mod 4), right end R′ = W − c − 1 even and
at least 2, and the map of a step from (E, R, L) to (W, R′, L₁′), with L₁′ = `loopL1 b c W`. -/
def Landing (n E R : Nat) (L : Int) (ms : List Mark) (W : Nat) : Prop :=
  ∃ k a b c R', ms = [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] ∧ a % 2 = 1 ∧ b % 2 = 0 ∧ W % 4 = 0 ∧ c + R' + 1 = W ∧
    R' % 2 = 0 ∧ 2 ≤ R' ∧ StepMap k n E R L W R' (loopL1 b c W)

/-- The round start is not three walls. -/
def NotWWW (ms : List Mark) : Prop := ∀ a b c, ms ≠ [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩]

/-- Where a stretch from a pass start of width E with right end R and left countdown L may end: after n rounds, with
end meetings `ds`, at the round start `ms`, `W`: the run left phase 0 or the halving chain, at a round start that is
not three walls, or it is at a landing of the loop's chain. -/
def EndEvent (E R : Nat) (L : Int) (n : Nat) (ds : List Nat) (ms : List Mark) (W : Nat) : Prop :=
  ((LeftPhase0 n ms ∨ ChainBreak ds) ∧ NotWWW ms) ∨ Landing n E R L ms W

/-- A phase-0 pass start with right end R and every gap at least 448: the start classes of the endgame trees. -/
def PassStart448 (ms : List Mark) (W R : Nat) : Prop :=
  ∃ a b, ms = [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] ∧ a % 2 = 1 ∧ b % 2 = 0 ∧ W % 2 = 0 ∧ R % 2 = 0 ∧ 2 ≤ R ∧
    448 ≤ a ∧ a + 448 ≤ b ∧ b + 448 + R + 1 ≤ W

/-- Where the loop's chain ends: an end event at which the run is not at a pass start with every gap at least 448 (a
round start that is not three walls, or a landing with a gap below 448); from a landing with every gap at least 448
the run is followed on. -/
def LoopEnd (E R : Nat) (L : Int) (n : Nat) (ds : List Nat) (ms : List Mark) (W : Nat) : Prop :=
  EndEvent E R L n ds ms W ∧ ¬ ∃ R', PassStart448 ms W R'

/-- A clean tape: only the end marker is left, at W − 2. -/
def CleanTape (ms : List Mark) (W : Nat) : Prop := ms = [⟨.M, W - 2⟩]

/-- Back at a loop state after a full pass: after 8 rounds, three walls at a, b, c with a odd, b even, c odd and
W even. -/
def LoopReturn (n : Nat) (ms : List Mark) (W : Nat) : Prop :=
  n = 8 ∧ ∃ a b c, ms = [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] ∧ a % 2 = 1 ∧ b % 2 = 0 ∧ c % 2 = 1 ∧ W % 2 = 0

/-- Where a stretch from a loop state may end: after n rounds, with end meetings `ds`, at the round start `ms`, `W`:
a clean tape, a break of the end-meeting chain, or a loop state again after a full pass. -/
def ExitEvent (n : Nat) (ds : List Nat) (ms : List Mark) (W : Nat) : Prop :=
  CleanTape ms W ∨ ChainBreak ds ∨ LoopReturn n ms W

/-- Which end events a tree's leaves end at: those of a stretch from a pass start, or from a loop state. -/
inductive EndSpec | endgame | exit

/-- The end events of `sp` (the width `E`, right end `R` and left countdown `L` of the start are used by `.endgame`
only). -/
def SpecEvent : EndSpec → Nat → Nat → Int → Nat → List Nat → List Mark → Nat → Prop
  | .endgame, E, R, L, n, ds, ms, W => EndEvent E R L n ds ms W
  | .exit, _, _, _, n, ds, ms, W => ExitEvent n ds ms W

theorem chainBreak_prefix {ds : List Nat} (h : ChainBreak ds) (p : List Nat) : ChainBreak (p ++ ds) := by
  obtain ⟨l₁, d, d', l₂, rfl, hn⟩ := h
  exact ⟨p ++ l₁, d, d', l₂, by simp, hn⟩

/-- No end event after zero rounds from a three-wall start of width E. -/
theorem not_endEvent_zero (E R : Nat) (L : Int) (a b c : Nat) :
    ¬ EndEvent E R L 0 [] [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E := by
  rintro (⟨-, h⟩ | ⟨k, _, _, _, _, -, -, -, -, -, -, -, hm⟩)
  · exact h a b c rfl
  · cases k <;> simp [StepMap] at hm

/-- No exit event after zero rounds from a loop state. -/
theorem not_exitEvent_zero (a b c E : Nat) : ¬ ExitEvent 0 [] [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E := by
  rintro (h | ⟨l₁, d, d', l₂, h, -⟩ | ⟨h, -⟩)
  · simp [CleanTape] at h
  · cases l₁ <;> simp at h
  · cases h

end BB6

namespace BB6.Sym
open BB6

/-- The start's width, right end and left countdown as forms, which a tree check carries along (substituted with the
start). -/
structure SForms where
  E : YForm
  R : YForm
  L : YForm

def SForms.subst (f : SForms) (i : Nat) (ε : Int) : SForms := ⟨f.E.subst i ε, f.R.subst i ε, f.L.subst i ε⟩
def SForms.skew (f : SForms) (i j : Nat) (s : Int) : SForms := ⟨f.E.skew i j s, f.R.skew i j s, f.L.skew i j s⟩

/-- At `y` the forms take the values E, R and L. -/
def SForms.Ag (y : List Int) (f : SForms) (E R : Nat) (L : Int) : Prop :=
  agN y f.E E ∧ agN y f.R R ∧ L = f.L.eval y

theorem SForms.ag_subst {z : List Int} {i : Nat} {ε : Int} (hi : i < z.length) {f : SForms} {E R : Nat} {L : Int}
    (h : f.Ag (lift z i ε) E R L) : (f.subst i ε).Ag z E R L :=
  ⟨agN_subst hi h.1, agN_subst hi h.2.1, by rw [h.2.2]; exact (eval_subst f.L i ε z hi).symm⟩

theorem SForms.ag_skew {z : List Int} {i j : Nat} {s : Int} (hi : i < z.length) (hj : j < z.length) {f : SForms}
    {E R : Nat} {L : Int} (h : f.Ag (skewLift z i j s) E R L) : (f.skew i j s).Ag z E R L :=
  ⟨agN_skew hi hj h.1, agN_skew hi hj h.2.1, by rw [h.2.2]; exact (eval_skew f.L i j s z hi hj).symm⟩

section
variable (ts : List YForm) (Γ : Int)

/-- `a ≠ b` at every point of the cone: a nonzero constant difference, a decided order, or an odd difference. -/
def neDec (a b : YForm) : Bool :=
  match (a.sub b).constVal with
  | some v => v != 0
  | none => ltDec a b ts Γ == some true || ltDec b a ts Γ == some true || (a.sub b).modDec 2 == some 1

theorem neDec_sound {y : List Int} (hy : inCone ts Γ y) {a b : YForm} (h : neDec ts Γ a b = true) :
    a.eval y ≠ b.eval y := by
  unfold neDec at h
  cases hc : (a.sub b).constVal with
  | some v =>
    rw [hc] at h
    have := eval_constVal _ v hc y
    simp only [eval_sub] at this
    simp only [bne_iff_ne, ne_eq] at h
    omega
  | none =>
    rw [hc] at h
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with (h | h) | h
    · have := (ltDec_sound a b ts Γ y hy true h).mpr rfl; omega
    · have := (ltDec_sound b a ts Γ y hy true h).mpr rfl; omega
    · have := eval_mod _ 2 1 h y
      simp only [eval_sub] at this
      omega

/-- The end meeting after one at distance `d` is decidedly not where the chain puts it. -/
def brkDec (d d' : YForm) : Bool :=
  if d.modDec 4 == some 0 then
    match d.half? with
    | some h => neDec ts Γ d' (h.addc 4)
    | none => false
  else if d.modDec 4 == some 2 then
    match (d.addc (-2)).half? with
    | some h => neDec ts Γ d' h
    | none => false
  else d.modDec 2 == some 1

theorem brkDec_sound {y : List Int} (hy : inCone ts Γ y) {d d' : YForm} {n n' : Nat} (hd : agN y d n)
    (hd' : agN y d' n') (h : brkDec ts Γ d d' = true) : ¬ ChainNext n n' := by
  unfold brkDec at h
  unfold agN at hd hd'
  unfold ChainNext
  split at h
  · rename_i h0
    simp only [beq_iff_eq] at h0
    have hm := eval_mod d 4 0 h0 y
    cases hh : d.half? with
    | none => rw [hh] at h; cases h
    | some g =>
      rw [hh] at h
      have e := eval_half d g hh y
      have ne := neDec_sound ts Γ hy h
      simp only [eval_addc] at ne
      omega
  · split at h
    · rename_i _ h2
      simp only [beq_iff_eq] at h2
      have hm := eval_mod d 4 2 h2 y
      cases hh : (d.addc (-2)).half? with
      | none => rw [hh] at h; cases h
      | some g =>
        rw [hh] at h
        have e := eval_half _ g hh y
        have ne := neDec_sound ts Γ hy h
        simp only [eval_addc] at e
        omega
    · simp only [beq_iff_eq] at h
      have hm := eval_mod d 2 1 h y
      omega

/-- Some two consecutive meetings of the list are decidedly off the chain. -/
def brkList : List YForm → Bool
  | d :: d' :: rest => brkDec ts Γ d d' || brkList (d' :: rest)
  | _ => false

theorem brkList_sound {y : List Int} (hy : inCone ts Γ y) :
    ∀ (fs : List YForm) (ns : List Nat), agLN y fs ns → brkList ts Γ fs = true → ChainBreak ns
  | d :: d' :: rest, n :: n' :: ns, h, hb => by
    simp only [brkList, Bool.or_eq_true] at hb
    rcases hb with hb | hb
    · exact ⟨[], n, n', ns, rfl, brkDec_sound ts Γ hy h.1 h.2.1 hb⟩
    · exact chainBreak_prefix (brkList_sound hy (d' :: rest) (n' :: ns) h.2 hb) [n]
  | [], _, _, hb => by simp [brkList] at hb
  | [_], _, _, hb => by simp [brkList] at hb
  | _ :: _ :: _, [], h, _ => absurd h id
  | _ :: _ :: _, [_], h, _ => absurd h.2 id

theorem agL_types {y : List Int} : ∀ {ss : List SMark} {ms : List Mark}, agL y ss ms →
    ss.map SMark.t = ms.map Mark.t
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp only [List.map_cons, h.1.1, agL_types h.2]
  | [], _ :: _, h => absurd h id
  | _ :: _, [], h => absurd h id

/-- The run has left phase 0 (`LeftPhase0`), at the round start reached after `n` rounds. -/
def leftP0Check (n : Nat) (ss : List SMark) : Bool :=
  (n == 1 && !decide (ss.map SMark.t = [.B, .W])) || (n == 2 && !decide (ss.map SMark.t = [.M, .B]))

theorem leftP0Check_sound {y : List Int} {n : Nat} {ss : List SMark} {ms : List Mark} (hs : agL y ss ms)
    (h : leftP0Check n ss = true) : LeftPhase0 n ms := by
  unfold leftP0Check at h
  rw [agL_types hs] at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_false_iff_not] at h
  exact h

/-- The round start is not three walls when its forms are not. -/
theorem notWWW_of_none {y : List Int} {ss : List SMark} {ms : List Mark} (hs : agL y ss ms) (h : swwwOf ss = none) :
    NotWWW ms := by
  intro a b c hm
  have := (wwwOf_agree hs).1 h
  rw [hm] at this
  simp [wwwOf] at this

/-- The map of a step of kind `k` as identities of forms (`StepMap`): `f` the start's forms, `n` the rounds, `sW`,
`R'`, `L'` the landing's width, right end and left countdown. -/
def stepMapCheck (f : SForms) (n : Nat) (sW R' L' : YForm) : StepKind → Bool
  | .full => n == 8 && sameForm (R'.smul 16) f.R && sameForm (L'.smul 64) f.L && sameForm sW (f.E.addc 24)
  | .half => n == 2 && sameForm (R'.smul 2) f.R &&
      sameForm (L'.smul 2) (((f.L.add (f.E.smul 35)).sub (f.R.smul 147)).addc (-60)) &&
      sameForm sW (f.E.addc 6) && f.E.modDec 4 == some 2
  | .break7 => n == 7 && sameForm (R'.smul 4704) ((((f.E.smul 476).add (f.R.smul 980)).sub f.L).addc 15984) &&
      sameForm (L'.smul 96) (((f.L.add (f.E.smul 1120)).add (f.R.smul 1666)).addc 50328) &&
      sameForm sW (f.E.addc 24)

theorem stepMapCheck_sound {y : List Int} {f : SForms} {E R : Nat} {L : Int} (hf : f.Ag y E R L) {n : Nat}
    {sW R' L' : YForm} {W R'v : Nat} (hW : agN y sW W) (hR' : agN y R' R'v) {k : StepKind}
    (h : stepMapCheck f n sW R' L' k = true) : StepMap k n E R L W R'v (L'.eval y) := by
  obtain ⟨hE, hR, hL⟩ := hf
  unfold agN at hE hR hW hR'
  cases k with
  | full =>
    simp only [stepMapCheck, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hn, e1⟩, e2⟩, e3⟩ := h
    have q1 := sameForm_sound e1 y
    have q2 := sameForm_sound e2 y
    have q3 := sameForm_sound e3 y
    simp only [eval_smul, eval_addc] at q1 q2 q3
    exact ⟨hn, by omega, by omega, by omega⟩
  | half =>
    simp only [stepMapCheck, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨hn, e1⟩, e2⟩, e3⟩, e4⟩ := h
    have q1 := sameForm_sound e1 y
    have q2 := sameForm_sound e2 y
    have q3 := sameForm_sound e3 y
    have m4 := eval_mod _ 4 2 e4 y
    simp only [eval_smul, eval_addc, eval_add, eval_sub] at q1 q2 q3
    exact ⟨hn, by omega, by omega, by omega, by omega⟩
  | break7 =>
    simp only [stepMapCheck, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hn, e1⟩, e2⟩, e3⟩ := h
    have q1 := sameForm_sound e1 y
    have q2 := sameForm_sound e2 y
    have q3 := sameForm_sound e3 y
    simp only [eval_smul, eval_addc, eval_add, eval_sub] at q1 q2 q3
    exact ⟨hn, by omega, by omega, by omega⟩

/-- The round start is a landing of the loop's chain (`Landing`) after `n` rounds from the start with forms `f`:
three walls with the phase-0 parities decided, a right end decidedly at least 2, and the map of one of the steps. -/
def landingCheck (f : SForms) (n : Nat) (ss : List SMark) (sW : YForm) : Bool :=
  match swwwOf ss with
  | none => false
  | some (a, b, c) =>
    let R' := (sW.sub c).addc (-1)
    let L' := L1Form b c sW
    a.modDec 2 == some 1 && b.modDec 2 == some 0 && sW.modDec 4 == some 0 && R'.modDec 2 == some 0 &&
    ltDec (YForm.const 1) R' ts Γ == some true &&
    (stepMapCheck f n sW R' L' .full || stepMapCheck f n sW R' L' .half || stepMapCheck f n sW R' L' .break7)

theorem landingCheck_sound {y : List Int} (hy : inCone ts Γ y) {f : SForms} {E R : Nat} {L : Int}
    (hf : f.Ag y E R L) {n : Nat} {ss : List SMark} {sW : YForm} {ms : List Mark} {W : Nat} (hs : agL y ss ms)
    (hW : agN y sW W) (h : landingCheck ts Γ f n ss sW = true) : Landing n E R L ms W := by
  have hag := wwwOf_agree hs
  unfold landingCheck at h
  cases hsw : swwwOf ss with
  | none => rw [hsw] at h; cases h
  | some fs =>
    obtain ⟨fa, fb, fc⟩ := fs
    rw [hsw] at h
    obtain ⟨a, b, c, rfl, h1, h2, h3⟩ := hag.2 fa fb fc hsw
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨pa, pb⟩, pW⟩, pR⟩, g2⟩, hk⟩ := h
    have ma := modDec_nat h1 (m := 2) pa
    have mb := modDec_nat h2 (m := 2) pb
    have mW := modDec_nat hW (m := 4) pW
    have l2 := (ltDec_sound _ _ ts Γ y hy true g2).mpr rfl
    have pR' := eval_mod _ 2 0 pR y
    have hL' : loopL1 b c W = (L1Form fb fc sW).eval y := by
      have h2' := h2
      have h3' := h3
      have hW' := hW
      unfold agN at h2' h3' hW'
      rw [eval_L1Form, ← h2', ← h3', ← hW']; simp only [loopL1]
    have h3' := h3
    have hW' := hW
    unfold agN at h3' hW'
    simp only [eval_const, eval_addc, eval_sub] at l2 pR'
    have hR'ag : agN y ((sW.sub fc).addc (-1)) (W - c - 1) := by
      unfold agN; simp only [eval_addc, eval_sub]; omega
    have key : ∀ k, stepMapCheck f n sW ((sW.sub fc).addc (-1)) (L1Form fb fc sW) k = true →
        Landing n E R L [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] W := fun k hk' =>
      ⟨k, a, b, c, W - c - 1, rfl, by omega, by omega, by omega, by omega, by omega, by omega,
        by rw [hL']; exact stepMapCheck_sound hf hW hR'ag hk'⟩
    rcases hk with (hk | hk) | hk
    · exact key _ hk
    · exact key _ hk
    · exact key _ hk

end

/-! ## The last end meeting so far -/

/-- The last element of `l ++ ds`, with `l` an optional earlier last element. -/
def lastOf : Option YForm → List YForm → Option YForm
  | l, [] => l
  | _, d :: ds => lastOf (some d) ds

/-- `last` is the form of the last of the end meetings `prev` so far (when it is recorded). -/
def LastAg (y : List Int) (last : Option YForm) (prev : List Nat) : Prop :=
  ∀ f, last = some f → ∃ p₀ v, prev = p₀ ++ [v] ∧ agN y f v

theorem lastOf_ag {y : List Int} : ∀ (ds : List YForm) (ns : List Nat) (last : Option YForm) (prev : List Nat),
    LastAg y last prev → agLN y ds ns → LastAg y (lastOf last ds) (prev ++ ns)
  | [], [], _, prev, h, _ => by simpa [lastOf] using h
  | d :: ds, n :: ns, _, prev, _, hd => by
    have := lastOf_ag ds ns (some d) (prev ++ [n])
      (fun f hf => by cases hf; exact ⟨prev, n, rfl, hd.1⟩) hd.2
    simpa [lastOf] using this
  | [], _ :: _, _, _, _, hd => absurd hd id
  | _ :: _, [], _, _, _, hd => absurd hd id

theorem lastAg_subst {y : List Int} {i : Nat} {ε : Int} (hi : i < y.length) {last : Option YForm}
    {prev : List Nat} (h : LastAg (lift y i ε) last prev) : LastAg y (last.map (·.subst i ε)) prev := by
  intro f hf
  cases hl : last with
  | none => rw [hl] at hf; cases hf
  | some g =>
    rw [hl] at hf
    cases hf
    obtain ⟨p₀, v, hp, hv⟩ := h g hl
    exact ⟨p₀, v, hp, agN_subst hi hv⟩

theorem lastAg_skew {y : List Int} {i j : Nat} {s : Int} (hi : i < y.length) (hj : j < y.length)
    {last : Option YForm} {prev : List Nat} (h : LastAg (skewLift y i j s) last prev) :
    LastAg y (last.map (·.skew i j s)) prev := by
  intro f hf
  cases hl : last with
  | none => rw [hl] at hf; cases hf
  | some g =>
    rw [hl] at hf
    cases hf
    obtain ⟨p₀, v, hp, hv⟩ := h g hl
    exact ⟨p₀, v, hp, agN_skew hi hj hv⟩

/-- The break check at a leaf, with the last meeting before it. -/
theorem brkLast_sound {ts : List YForm} {Γ : Int} {y : List Int} (hy : inCone ts Γ y) {last : Option YForm}
    {prev : List Nat} (hl : LastAg y last prev) {ds : List YForm} {ns : List Nat} (hd : agLN y ds ns)
    (h : brkList ts Γ (last.toList ++ ds) = true) : ChainBreak (prev ++ ns) := by
  cases hlast : last with
  | none =>
    rw [hlast] at h
    exact chainBreak_prefix (brkList_sound ts Γ hy ds ns hd (by simpa using h)) prev
  | some f =>
    rw [hlast] at h
    obtain ⟨p₀, v, rfl, hv⟩ := hl f hlast
    have := brkList_sound ts Γ hy (f :: ds) (v :: ns) ⟨hv, hd⟩ (by simpa using h)
    simpa using chainBreak_prefix this p₀

/-! ## The end event at a leaf -/

section
variable (ts : List YForm) (Γ : Int)

/-- The round start is a clean tape (`CleanTape`). -/
def cleanCheck (ss : List SMark) (sW : YForm) : Bool :=
  match ss with
  | [m] => decide (m.t = .M) && eqDec m.p (sW.addc (-2)) ts Γ == some true
  | _ => false

theorem cleanCheck_sound {y : List Int} (hy : inCone ts Γ y) {ss : List SMark} {sW : YForm} {ms : List Mark}
    {W : Nat} (hs : agL y ss ms) (hW : agN y sW W) (h : cleanCheck ts Γ ss sW = true) : CleanTape ms W := by
  match ss, ms, hs with
  | [s], [m], hs =>
    obtain ⟨⟨ht, hp⟩, -⟩ := hs
    simp only [cleanCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨hM, he⟩ := h
    have he' := (eqDec_sound _ _ ts Γ y hy true he).mpr rfl
    unfold agN at hp hW
    simp only [eval_addc] at he'
    obtain ⟨t, p⟩ := m
    simp only at ht hp
    subst ht
    rw [hM]
    have hp2 : p = W - 2 := by omega
    rw [hp2]
    rfl
  | [], _, _ => simp [cleanCheck] at h
  | _ :: _ :: _, _, _ => simp [cleanCheck] at h
  | [_], [], hs => exact absurd hs id
  | [_], _ :: _ :: _, hs => exact absurd hs.2 id

/-- Eight rounds, and the round start is a loop state (`LoopReturn`). -/
def loopRetCheck (n : Nat) (ss : List SMark) (sW : YForm) : Bool :=
  n == 8 &&
  match swwwOf ss with
  | none => false
  | some (a, b, c) => a.modDec 2 == some 1 && b.modDec 2 == some 0 && c.modDec 2 == some 1 && sW.modDec 2 == some 0

theorem loopRetCheck_sound {y : List Int} {n : Nat} {ss : List SMark} {sW : YForm} {ms : List Mark} {W : Nat}
    (hs : agL y ss ms) (hW : agN y sW W) (h : loopRetCheck n ss sW = true) : LoopReturn n ms W := by
  have hag := wwwOf_agree hs
  unfold loopRetCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hn, h⟩ := h
  cases hsw : swwwOf ss with
  | none => rw [hsw] at h; cases h
  | some f =>
    obtain ⟨fa, fb, fc⟩ := f
    rw [hsw] at h
    obtain ⟨a, b, c, rfl, h1, h2, h3⟩ := hag.2 fa fb fc hsw
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨pa, pb⟩, pc⟩, pW⟩ := h
    have ma := modDec_nat h1 (m := 2) pa
    have mb := modDec_nat h2 (m := 2) pb
    have mc := modDec_nat h3 (m := 2) pc
    have mW := modDec_nat hW (m := 2) pW
    exact ⟨hn, a, b, c, rfl, by omega, by omega, by omega, by omega⟩

/-- The end event of `sp` at a leaf: after `n` rounds, with the end meeting forms `ds` (the last one before the leaf's
subtree first), at the round start `ss`, `sW`; `f` holds the start's width, right end and left countdown. -/
def evCheck (sp : EndSpec) (n : Nat) (ds : List YForm) (f : SForms) (ss : List SMark) (sW : YForm) : Bool :=
  match sp with
  | .endgame => landingCheck ts Γ f n ss sW || ((leftP0Check n ss || brkList ts Γ ds) && (swwwOf ss).isNone)
  | .exit => cleanCheck ts Γ ss sW || brkList ts Γ ds || loopRetCheck n ss sW

theorem evCheck_sound (sp : EndSpec) {y : List Int} (hy : inCone ts Γ y) {f : SForms} {E R : Nat} {L : Int}
    (hf : f.Ag y E R L) {n : Nat} {last : Option YForm} {prev : List Nat} (hl : LastAg y last prev)
    {ds : List YForm} {ns : List Nat} (hd : agLN y ds ns) {ss : List SMark} {ms : List Mark} {sW : YForm} {W : Nat}
    (hs : agL y ss ms) (hW : agN y sW W) (h : evCheck ts Γ sp n (last.toList ++ ds) f ss sW = true) :
    SpecEvent sp E R L n (prev ++ ns) ms W := by
  cases sp with
  | endgame =>
    simp only [evCheck, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h | h, hn⟩
    · exact Or.inr (landingCheck_sound ts Γ hy hf hs hW h)
    · exact Or.inl ⟨Or.inl (leftP0Check_sound hs h), notWWW_of_none hs (Option.isNone_iff_eq_none.mp hn)⟩
    · exact Or.inl ⟨Or.inr (brkLast_sound hy hl hd h), notWWW_of_none hs (Option.isNone_iff_eq_none.mp hn)⟩
  | exit =>
    simp only [evCheck, Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · exact Or.inl (cleanCheck_sound ts Γ hy hs hW h)
    · exact Or.inr (Or.inl (brkLast_sound hy hl hd h))
    · exact Or.inr (Or.inr (loopRetCheck_sound hs hW h))

end

/-! ## Trees whose leaves end at an end event -/

variable (Γ : Int) (fuel : Nat)

/-- The class of the left countdown a close leaf shows: `L % m = c`, when `cls = some (m, c)`. -/
def clsCheck (cls : Option (Int × Int)) (sL : YForm) : Bool :=
  match cls with
  | some (m, c) => sL.modDec m == some c
  | none => false

/-- As `Tree.okNC`, and each leaf's run ends at an end event of `sp` (`evCheck`; `r0`: the rounds before this
subtree, `last`: the last end meeting before it).  For `.endgame` (`EndEvent`): it left phase 0 or its end meetings
left the chain, at a round start that is not three walls, or it is at a landing of the loop's chain (`Landing`); for
`.exit` (`ExitEvent`): a clean tape, a break of the chain, or a loop state again after 8 rounds.  Or the leaf is a
close leaf, at which the left countdown `f.L` is decidedly in the class `cls`.  The start's forms `f` and `last` are
substituted along with the start. -/
def Tree.okEnd (k : Nat) (cls : Option (Int × Int)) (sp : EndSpec) :
    Tree → Bool → List SMark → YForm → List YForm → SForms → Nat → Option YForm → Bool
  | .leaf n, wf, ss, sW, ts, f, r0, last =>
    clsCheck cls f.L ||
    ((wf || symRightOK ts Γ (YForm.const 4) false sW ss) &&
     (match symMeetsRounds ts Γ fuel n ss sW with
      | some ds => allGe3 ts Γ ds &&
        (match symRoundsZ ts Γ fuel n ss sW with
         | some (.newRound ss' sW') => evCheck ts Γ sp (r0 + n) (last.toList ++ ds) f ss' sW'
         | _ => false)
      | none => false))
  | .adv n t, wf, ss, sW, ts, f, r0, last =>
    (wf || symRightOK ts Γ (YForm.const 4) false sW ss) &&
    (match symMeetsRounds ts Γ fuel n ss sW with
     | some ds => allGe3 ts Γ ds &&
       (match symRoundsZ ts Γ fuel n ss sW with
        | some (.newRound ss' sW') => t.okEnd k cls sp true ss' sW' ts f (r0 + n) (lastOf last ds)
        | _ => false)
     | none => false)
  | .node i t0 t1, wf, ss, sW, ts, f, r0, last =>
    decide (i < k) &&
      t0.okEnd k cls sp wf (substL ss i 0) (sW.subst i 0) (substT ts i 0) (f.subst i 0) r0
        (last.map (·.subst i 0)) &&
      t1.okEnd k cls sp wf (substL ss i 1) (sW.subst i 1) (substT ts i 1) (f.subst i 1) r0
        (last.map (·.subst i 1))
  | .skew i j s t, wf, ss, sW, ts, f, r0, last =>
    decide (i < k) && decide (j < k) && decide (i ≠ j) &&
      t.okEnd k cls sp wf (skewL ss i j s) (sW.skew i j s) (skewT ts i j s) (f.skew i j s) r0
        (last.map (·.skew i j s))

/-- The check's state at a subtree: the start state and the start's forms (substituted along with the start). -/
abbrev EState := SState × SForms

def esSplit (es : EState) (i : Nat) (ε : Int) : EState := (stSplit es.1 i ε, es.2.subst i ε)
def esSkew (es : EState) (i j : Nat) (s : Int) : EState := (stSkew es.1 i j s, es.2.skew i j s)

variable {Γ fuel} in
theorem Tree.okEnd_node {k i : Nat} {cls : Option (Int × Int)} {sp : EndSpec} {wf : Bool} {t0 t1 : Tree}
    {es : EState} (hi : i < k)
    (h0 : t0.okEnd Γ fuel k cls sp wf (esSplit es i 0).1.1 (esSplit es i 0).1.2.1 (esSplit es i 0).1.2.2
      (esSplit es i 0).2 0 none = true)
    (h1 : t1.okEnd Γ fuel k cls sp wf (esSplit es i 1).1.1 (esSplit es i 1).1.2.1 (esSplit es i 1).1.2.2
      (esSplit es i 1).2 0 none = true) :
    (Tree.node i t0 t1).okEnd Γ fuel k cls sp wf es.1.1 es.1.2.1 es.1.2.2 es.2 0 none = true := by
  simp only [Tree.okEnd, Bool.and_eq_true, decide_eq_true_eq, Option.map_none]; exact ⟨⟨hi, h0⟩, h1⟩

variable {Γ fuel} in
theorem Tree.okEnd_skew {k i j : Nat} {cls : Option (Int × Int)} {sp : EndSpec} {wf : Bool} {s : Int} {t : Tree}
    {es : EState} (hi : i < k) (hj : j < k) (hij : i ≠ j)
    (h : t.okEnd Γ fuel k cls sp wf (esSkew es i j s).1.1 (esSkew es i j s).1.2.1 (esSkew es i j s).1.2.2
      (esSkew es i j s).2 0 none = true) :
    (Tree.skew i j s t).okEnd Γ fuel k cls sp wf es.1.1 es.1.2.1 es.1.2.2 es.2 0 none = true := by
  simp only [Tree.okEnd, Bool.and_eq_true, decide_eq_true_eq, Option.map_none]; exact ⟨⟨⟨hi, hj⟩, hij⟩, h⟩

/-- **A checked end tree, for the machine.**  At every point of the root class inside the cone, where the start's
forms `f` take the values E, R and L, either the left countdown L is in the class `cls` (a close leaf), or the machine
runs from the round start for the rounds recorded on the way to the leaf without halting, reaching a round start,
every end meeting on the way is at distance at least 3, and the run ends at an end event of `sp` (`SpecEvent`; `r0`
rounds and the end meetings `prev` before this subtree). -/
theorem Tree.soundEnd (k : Nat) (cls : Option (Int × Int)) (sp : EndSpec) (t : Tree) :
    ∀ (wf : Bool) (ss : List SMark) (sW : YForm) (ts : List YForm) (f : SForms) (r0 : Nat) (last : Option YForm),
    t.okEnd Γ fuel k cls sp wf ss sW ts f r0 last = true → ∀ (y : List Int), y.length = k → inCone ts Γ y →
    ∀ (ms : List Mark) (Wn E R : Nat) (L : Int) (prev : List Nat), agL y ss ms → agN y sW Wn → f.Ag y E R L →
    (wf = true → roundWF ms Wn) → LastAg y last prev →
    (∃ m c, cls = some (m, c) ∧ L % m = c) ∨
    ∃ n kk ms' Wn', steps kk (roundStart ms Wn) = some (roundStart ms' Wn') ∧
      roundsZ fuel n ms Wn = .newRound ms' Wn' ∧ (∀ d ∈ meetsRounds fuel n ms Wn, 3 ≤ d) ∧
      SpecEvent sp E R L (r0 + n) (prev ++ meetsRounds fuel n ms Wn) ms' Wn' := by
  induction t with
  | leaf n =>
    intro wf ss sW ts f r0 last h y _ hy ms Wn E R L prev hs hW hf hwf hlast
    simp only [Tree.okEnd] at h
    rcases (Bool.or_eq_true _ _).mp h with hc | h'
    · left
      unfold clsCheck at hc
      cases hcls : cls with
      | none => rw [hcls] at hc; cases hc
      | some p =>
        obtain ⟨m, c⟩ := p
        rw [hcls] at hc
        simp only [beq_iff_eq] at hc
        exact ⟨m, c, rfl, by rw [hf.2.2]; exact eval_mod f.L m c hc y⟩
    · right
      simp only [Bool.and_eq_true] at h'
      obtain ⟨hwf', hmt⟩ := h'
      have hrwf := wf_of_check Γ hy hs hW hwf hwf'
      cases hmr : symMeetsRounds ts Γ fuel n ss sW with
      | none => rw [hmr] at hmt; cases hmt
      | some ds =>
        rw [hmr] at hmt
        simp only [Bool.and_eq_true] at hmt
        obtain ⟨hge3, hrun⟩ := hmt
        have hds := symMeetsRounds_sound ts Γ hy fuel n ss ms sW Wn ds hs hW hmr
        have hge := allGe3_sound ts Γ hy hds hge3
        cases hr : symRoundsZ ts Γ fuel n ss sW with
        | none => rw [hr] at hrun; cases hrun
        | some r =>
          rw [hr] at hrun
          cases r with
          | newRound ss' sW' =>
            have hag := symRoundsZ_sound ts Γ hy fuel n ss ms sW Wn _ hs hW hr
            generalize hcr : roundsZ fuel n ms Wn = cr at hag
            cases cr with
            | newRound ms' Wn' =>
              obtain ⟨kk, hk, -⟩ := rounds_run fuel n ms Wn hrwf (by rw [hcr]; intro h; cases h)
              rw [hcr] at hk
              exact ⟨n, kk, ms', Wn', hk, hcr, hge, evCheck_sound ts Γ sp hy hf hlast hds hag.1 hag.2 hrun⟩
            | _ => exact absurd hag id
          | _ => simp at hrun
  | adv n t ih =>
    intro wf ss sW ts f r0 last h y hlen hy ms Wn E R L prev hs hW hf hwf hlast
    simp only [Tree.okEnd, Bool.and_eq_true] at h
    obtain ⟨hwf', hmt⟩ := h
    have hrwf := wf_of_check Γ hy hs hW hwf hwf'
    cases hmr : symMeetsRounds ts Γ fuel n ss sW with
    | none => rw [hmr] at hmt; cases hmt
    | some ds =>
      rw [hmr] at hmt
      simp only [Bool.and_eq_true] at hmt
      obtain ⟨hge3, hrun⟩ := hmt
      have hds := symMeetsRounds_sound ts Γ hy fuel n ss ms sW Wn ds hs hW hmr
      have hge := allGe3_sound ts Γ hy hds hge3
      cases hr : symRoundsZ ts Γ fuel n ss sW with
      | none => rw [hr] at hrun; cases hrun
      | some r =>
        rw [hr] at hrun
        cases r with
        | newRound ss' sW' =>
          have hag := symRoundsZ_sound ts Γ hy fuel n ss ms sW Wn _ hs hW hr
          generalize hcr : roundsZ fuel n ms Wn = cr at hag
          cases cr with
          | newRound ms' Wn' =>
            obtain ⟨kk, hk, hw'⟩ := rounds_run fuel n ms Wn hrwf (by rw [hcr]; intro h; cases h)
            rw [hcr] at hk hw'
            rcases ih true ss' sW' ts f (r0 + n) (lastOf last ds) hrun y hlen hy ms' Wn' E R L
                (prev ++ meetsRounds fuel n ms Wn) hag.1 hag.2 hf (fun _ => hw')
                (lastOf_ag ds _ last prev hlast hds) with hc | ⟨n₂, kk₂, ms'', Wn'', hk₂, hr₂, hge₂, hev⟩
            · exact Or.inl hc
            · right
              refine ⟨n + n₂, kk + kk₂, ms'', Wn'', steps_seq hk hk₂, ?_, ?_, ?_⟩
              · rw [roundsZ_add fuel n n₂ ms Wn ms' Wn' hcr]; exact hr₂
              · rw [meetsRounds_append fuel n n₂ ms Wn ms' Wn' hcr]
                intro d hd
                rcases List.mem_append.mp hd with hd | hd
                · exact hge d hd
                · exact hge₂ d hd
              · rw [meetsRounds_append fuel n n₂ ms Wn ms' Wn' hcr, ← List.append_assoc, ← Nat.add_assoc]
                exact hev
          | _ => exact absurd hag id
        | _ => simp at hrun
  | node i t0 t1 ih0 ih1 =>
    intro wf ss sW ts f r0 last h y hlen hy ms Wn E R L prev hs hW hf hwf hlast
    simp only [Tree.okEnd, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hi, h0⟩, h1⟩ := h
    obtain ⟨ε, z, hε, hzl, rfl⟩ := cover_split y i (by omega)
    have hiz : i < z.length := by omega
    rcases hε with rfl | rfl
    · exact ih0 _ _ _ _ _ _ _ h0 z (by rw [hzl]; exact hlen) (inCone_subst hiz hy) ms Wn E R L prev
        (agL_subst hiz hs) (agN_subst hiz hW) (SForms.ag_subst hiz hf) hwf (lastAg_subst hiz hlast)
    · exact ih1 _ _ _ _ _ _ _ h1 z (by rw [hzl]; exact hlen) (inCone_subst hiz hy) ms Wn E R L prev
        (agL_subst hiz hs) (agN_subst hiz hW) (SForms.ag_subst hiz hf) hwf (lastAg_subst hiz hlast)
  | skew i j s t ih =>
    intro wf ss sW ts f r0 last h y hlen hy ms Wn E R L prev hs hW hf hwf hlast
    simp only [Tree.okEnd, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hi, hj⟩, hij⟩, ht⟩ := h
    obtain ⟨z, hzl, rfl⟩ := cover_skew y i j s hij (by omega)
    have hiz : i < z.length := by omega
    have hjz : j < z.length := by omega
    exact ih _ _ _ _ _ _ _ ht z (by rw [hzl]; exact hlen) (inCone_skew hiz hjz hy) ms Wn E R L prev
      (agL_skew hiz hjz hs) (agN_skew hiz hjz hW) (SForms.ag_skew hiz hjz hf) hwf (lastAg_skew hiz hjz hlast)

end BB6.Sym
