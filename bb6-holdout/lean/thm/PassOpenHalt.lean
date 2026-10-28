import PassHaltClasses
import CleanTheorem

/-!
# Pass starts with R ≥ 178 that halt, open at every depth

`blank_halt_small` puts the pass start that a halt from blank tape needs at R ≥ 178, in a cut leaf of `passTreeSym` at
every depth, and the second question of `never_halts_of_open` is whether the machine halts from such a pass start, of
width above 2⁴¹, that the run reaches from a clean tape.  This file shows that the pass start alone cannot answer it:
at every width there are pass starts with R ≥ 178 from which the machine halts and which `passTreeSym` leaves open at
every depth.

The first one was found by sampling: walls at 1,523, 2,010 and 2,477, width 2,656 (R = 178).  Its run leaves phase 0
of the loop in round 2, where the end is met at 176 = R − 2, and reaches no landing and no clean tape.  In round 5 the
end is met at 254 = 2⁸ − 2, which does not continue the chain of the meeting before, and that meeting's own halving
chain (254, 126, 62, 30, 14, 6, 2, 0) runs through three-wall round starts with R = 32, 16 and 2 (the one with R = 16 a
pass start in a halting class) to the close in round 19.  The route depends on the right end and the two walls next to
it, not on the first wall.  The family here is that start with its first wall anywhere (odd, at least 448 and at least
448 before the second) and its other two walls and its right end moved right together by any multiple of 2¹⁴: walls at
a, b and b + 467, width b + 646, b ≡ 2,010 (mod 2¹⁴).  (Untrusted: moved by odd multiples of 2¹³, none of 2,000 starts
closes.)

* `symOpenRun`: the model's rounds on a class, on symbolic positions (`symRoundsZ`): no round start before round N
  might be a checkpoint of `pass_next` (`mayCheckpoint`: three walls after 2, 7 or 8 rounds, as a landing of the loop's
  chain is, or a lone marker, as a clean tape is), and round N is left uncovered.  `symOpenRun_sound` is the statement
  for each member, and with `no_checkpoint` and `pass_next` a member with R ≥ 178 lies in a cut leaf of `passTreeSym`
  at every depth (`sym_open_of_run`).
* `symOpenRun2`: the same, except that a three-wall round start after 2, 7 or 8 rounds also passes when it is
  decidedly not a landing (`notLandingCheck`: for the step of the loop's chain that takes that many rounds, the
  identity of `StepMap` for the right end, the left countdown or the width is decidedly false on the class).
  `symOpenRun2_sound` and `sym_open_of_run2` as before; the families below are checked with it (`Fam.ok`).
* `family_open_halt`: every member of the family is a pass start with every gap at least 448 that `passTreeSym` leaves
  open at every depth (`symOpenRun` on the family, 19 rounds) and from which the machine halts (the close run on the
  family, `symCloseRun_halt`).  Both runs are evaluated by the kernel (`decide +kernel`, under a second).
* `sym_open_halt`: such pass starts at every width; `sym_open_halt_wide`: one wider than 2⁴¹ (`directWidth`).
* `open_halt_families`: eight families of the same kind, `family_open_halt`'s among them (`Fam.open_halt` proves one
  from its checks).  An untrusted scan of every pass start with R ≥ 178 and width from 2,048 to 3,072 (three first
  walls for each placement of the other walls, 75 million placements) finds eleven placements whose run closes, each
  for every first wall; seven of them repeat with the other walls and the width moved by any multiple of 2¹³ to 2¹⁵,
  and are the first seven families (for the other four the close run fails on every such class up to 2²⁹; for one of
  them the route was seen to depend on the width itself).  The eighth has width 13,400 and R = 186.
* `full_pass_open_halt`: a member of the eighth family is the landing of a full pass of the loop's chain, from a pass
  start with R = 2,976.  So the loop's chain can end at an open pass start with R ≥ 178 that halts after a full pass
  too, not only at a loop entry.  (Untrusted: of the 18.4 million points with R ≥ 178 and width up to 16,384 where a
  full pass from a pass start with every gap at least 448 can land, two close, at widths 13,400 and 16,292, both real
  landings.)
* `reentry_open_halt`: the eighth family's route at larger scales.  Its run meets the end at 184 = R − 2, then off the
  chain at 1,022 = 2¹⁰ − 2, and from there the end meetings halve, 510, 254, ..., 2, 0, through three-wall round
  starts with small right ends (R = 128, 64, 8 and 4), to the close.  On this route the meeting off the chain is at
  (W − b + 2R + 14)/4, so W − b = 2^(j+2) − 2R − 22 puts it at 2^j − 2, and for each j from 10 to 30 a family with
  R = 178 there halts, open at every depth (`reentryFams_shape`; on a member, the meetings are 176, 2^j − 2,
  2^(j−1) − 2, ..., 2, 0).  (Untrusted: a symbolic search of the model's rounds finds, for each such j and each
  R ≡ 2 (mod 4) tried, exactly one class of b that closes, modulo about 2^(1.5 j + 2).)
* `reentry6_open_halt`: the same with R = 182, for each j from 10 to 30 (`reentryFams6_shape`).  With R ≡ 6 (mod 8)
  the run has three walls in round 5 (width ≡ 2 mod 4) and in round 7, its half pass, with right end
  R′ = (W − b + 2R + 22)/16 = 2^(j−2).  That is no landing: a break of the loop's chain at round 7 would need
  4,704 R′ = 476 W + 980 R − L₁ + 15,984, and on the class the difference is −294 (W − b) − 441 b − 9,702 < 0, so
  `symOpenRun2` passes it.  From there full passes run to the close.
* `full_pass_open_halt6`: as `full_pass_open_halt`, a full pass of the loop's chain from a pass start with R = 3,552
  lands at width 29,404 on a pass start with R = 222 ≡ 6 (mod 8) (the class of the scale j = 11), open at every depth,
  from which the machine halts.
* `no_pass_open_halt`: four families with R = 230 (W − b = 1,570 and 3,618) that halt, open at every depth, and whose
  run meets no three-wall round start after the first (`symNoWWWRun`, round by round on the class): the end is met at
  228, then at 510 or 1,022 off the loop's chain, and the meetings halve to the close through round starts with four
  walls or with a marker or a block.  So no pass start lies between such a start and its halt.  (Untrusted: a census
  of R = 230 with W − b up to 8,192 finds no others.)
* `lane486_open_halt`: two lanes with R = 486, at each scale W − b = 2^(12+s) − 1,630 from s = 0 to 18
  (Q = W − b + 2R + 22 = 2^(12+s) − 636; `lane486_shape`).  The run meets the end at 484 = R − 2, then off the chain
  at Q/4 − 3 = 2^(10+s) − 162, whose chain runs 2^(9+s) − 82, ..., 2^(6+s) − 12, 2^(5+s) − 2, ..., 2, 0.  On the
  first lane its first three-wall round start after the first is in round 17, with width ≡ 2 (mod 4) and right end
  (Q + 636)/1,024; on the second in round 13, with right end (Q + 636)/256.  Each start's half pass begins full
  passes to the close.  (Untrusted: the same lanes close at every R ≡ 486 (mod 512), resp. (mod 1,024), tried up to
  4,582, with one class of b at each scale.)
-/

namespace BB6

open Sym

/-- Once the model's run leaves a round uncovered, it stays so. -/
theorem roundsZ_uncovered_add (fuel : Nat) : ∀ (n k : Nat) (ms : List Mark) (W : Nat),
    roundsZ fuel n ms W = .uncovered → roundsZ fuel (n + k) ms W = .uncovered
  | 0, _, _, _, h => by simp [roundsZ] at h
  | n + 1, k, ms, W, h => by
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [roundsZ] at h ⊢
    generalize roundZ fuel [] 1 ms W = r at h ⊢
    cases r with
    | newRound a b => exact roundsZ_uncovered_add fuel n k a b h
    | _ => exact h

/-- A round start after `r` rounds, with marks of these types, that might be a checkpoint of `pass_next`: three walls
after 2, 7 or 8 rounds (the steps of the loop's chain), or a lone marker. -/
def typesMayCheckpoint (r : Nat) : List MarkT → Bool
  | [.W, .W, .W] => r == 2 || r == 7 || r == 8
  | [.M] => true
  | _ => false

/-- The model's outcome after `r` rounds might be a checkpoint of `pass_next`. -/
def mayCheckpoint (r : Nat) : PR' → Bool
  | .newRound ms _ => typesMayCheckpoint r (ms.map (·.t))
  | _ => false

theorem mayCheckpoint_of {r W R : Nat} {L : Int} {ms' : List Mark} {W' : Nat}
    (h : Landing r W R L ms' W' ∨ (0 < r ∧ CleanTape ms' W' ∧ W < W')) :
    mayCheckpoint r (.newRound ms' W') = true := by
  rcases h with ⟨k, a, b, c, R', rfl, -, -, -, -, -, -, hS, -⟩ | ⟨-, rfl, -⟩
  · have hr : r = 8 ∨ r = 2 ∨ r = 7 := by
      cases k <;> simp only [StepMap] at hS <;> omega
    rcases hr with rfl | rfl | rfl <;> rfl
  · rfl

/-- **No checkpoint before the close.**  If the model's run from a round start leaves round N + 1 uncovered and none of
the round starts before it might be a checkpoint, then no round start of the run is a landing of the loop's chain or a
wider one-marker clean tape. -/
theorem no_checkpoint {fuel N : Nat} {ms : List Mark} {W R : Nat} {L : Int} (hN : roundsZ fuel N ms W = .uncovered)
    (hc : ∀ r < N, mayCheckpoint r (roundsZ fuel r ms W) = false) {r : Nat} {ms' : List Mark} {W' : Nat}
    (hr : roundsZ fuel r ms W = .newRound ms' W') :
    ¬ (Landing r W R L ms' W' ∨ (0 < r ∧ CleanTape ms' W' ∧ W < W')) := by
  intro h
  by_cases hrN : r < N
  · have := hc r hrN
    rw [hr, mayCheckpoint_of h] at this
    cases this
  · have := roundsZ_uncovered_add fuel N (r - N) ms W hN
    rw [show N + (r - N) = r by omega, hr] at this
    cases this

theorem closeClass_ge {R : Nat} (h : 178 ≤ R) : closeClass R = none := by
  unfold closeClass
  rw [Option.map_eq_none_iff, List.find?_eq_none]
  intro x hx
  simp only [closeClasses, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega

/-- **Open at every depth.**  A pass start with R ≥ 178 from which the model's run leaves a round uncovered before any
round start that might be a checkpoint of `pass_next` lies in a cut leaf of `passTreeSym` at every depth. -/
theorem sym_open_of_run {R a b W N : Nat} (hR : 178 ≤ R) (hP : PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R)
    (hN : roundsZ 1000 N [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W = .uncovered)
    (hc : ∀ r < N, mayCheckpoint r (roundsZ 1000 r [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = false) (d : Nat) :
    (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W : Int) / 2, (R : Int) / 2] = true := by
  rcases pass_next d R a b W hP with h | h | ⟨r, kk, ms', W', -, hr, hcp⟩
  · obtain ⟨a, b, m, c, -, hcl, -⟩ := h
    rw [closeClass_ge hR] at hcl
    cases hcl
  · simpa only [PassCut, show ¬ (R < 178) by omega, ↓reduceIte] using h
  · exact absurd (hcp.imp (fun h => h.2) id) (no_checkpoint hN hc hr)

/-- **Open at every depth**, as `sym_open_of_run`, from a run on which no round start before the round left uncovered
is a checkpoint of `pass_next`: neither a landing of the loop's chain nor a clean tape. -/
theorem sym_open_of_run2 {R a b W N : Nat} (hR : 178 ≤ R) (hP : PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R)
    (hN : roundsZ 1000 N [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W = .uncovered)
    (hc : ∀ r < N, ∀ ms' W', roundsZ 1000 r [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W = .newRound ms' W' →
      ¬ Landing r W R (passL1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) ms' W' ∧ ¬ CleanTape ms' W') (d : Nat) :
    (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W : Int) / 2, (R : Int) / 2] = true := by
  rcases pass_next d R a b W hP with h | h | ⟨r, kk, ms', W', -, hr, hcp⟩
  · obtain ⟨a, b, m, c, -, hcl, -⟩ := h
    rw [closeClass_ge hR] at hcl
    cases hcl
  · simpa only [PassCut, show ¬ (R < 178) by omega, ↓reduceIte] using h
  · by_cases hrN : r < N
    · obtain ⟨hL, hC⟩ := hc r hrN ms' W' hr
      rcases hcp with ⟨-, h⟩ | ⟨-, h, -⟩
      · exact absurd h hL
      · exact absurd h hC
    · have := roundsZ_uncovered_add 1000 N (r - N) _ W hN
      rw [show N + (r - N) = r by omega, hr] at this
      cases this

/-! ## The model's rounds on a class -/

/-- `mayCheckpoint` on a symbolic outcome: anything but a new round start might be one. -/
def symMayCheckpoint (r : Nat) : SPR → Bool
  | .newRound ss _ => typesMayCheckpoint r (ss.map (·.t))
  | _ => true

theorem agL_types {y : List Int} : ∀ {ss : List SMark} {ms : List Mark}, agL y ss ms → ss.map (·.t) = ms.map (·.t)
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    obtain ⟨⟨ht, -⟩, hr⟩ := h
    simp only [List.map_cons, ht, agL_types hr]
  | [], _ :: _, h => absurd h id
  | _ :: _, [], h => absurd h id

/-- The model's rounds on a class (cone `ts`, gaps ≥ Γ): no round start before round N might be a checkpoint, and
round N is left uncovered. -/
def symOpenRun (ts : List YForm) (Γ : Int) (N : Nat) (ss : List SMark) (sW : YForm) : Bool :=
  (List.range N).all (fun r => match symRoundsZ ts Γ 1000 r ss sW with
    | some sr => !symMayCheckpoint r sr
    | none => false) &&
  match symRoundsZ ts Γ 1000 N ss sW with
  | some .uncovered => true
  | _ => false

theorem symOpenRun_sound {ts : List YForm} {Γ : Int} {N : Nat} {ss : List SMark} {sW : YForm}
    (h : symOpenRun ts Γ N ss sW = true) {y : List Int} (hy : inCone ts Γ y) {ms : List Mark} {W : Nat}
    (hs : agL y ss ms) (hW : agN y sW W) :
    roundsZ 1000 N ms W = .uncovered ∧ ∀ r < N, mayCheckpoint r (roundsZ 1000 r ms W) = false := by
  simp only [symOpenRun, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨hc, hN⟩ := h
  constructor
  · cases e : symRoundsZ ts Γ 1000 N ss sW with
    | none => rw [e] at hN; cases hN
    | some sr =>
      have hag := symRoundsZ_sound ts Γ hy 1000 N ss ms sW W sr hs hW e
      rw [e] at hN
      cases sr with
      | uncovered =>
        generalize roundsZ 1000 N ms W = cr at hag ⊢
        cases cr with
        | uncovered => rfl
        | _ => exact absurd hag id
      | _ => cases hN
  · intro r hr
    have hcr := hc r hr
    cases e : symRoundsZ ts Γ 1000 r ss sW with
    | none => rw [e] at hcr; cases hcr
    | some sr =>
      have hag := symRoundsZ_sound ts Γ hy 1000 r ss ms sW W sr hs hW e
      rw [e] at hcr
      cases sr with
      | newRound ss' sW' =>
        generalize roundsZ 1000 r ms W = cr at hag ⊢
        cases cr with
        | newRound ms' W' =>
          simp only [symMayCheckpoint, Bool.not_eq_true'] at hcr
          simp only [mayCheckpoint, ← agL_types hag.1, hcr]
        | _ => exact absurd hag id
      | _ => simp [symMayCheckpoint] at hcr

/-! ## Round starts that are not landings -/

section
variable (ts : List YForm) (Γ : Int)

/-- A round start after `r` rounds, of width `sW` with right end `R'` and left countdown `L'`, is decidedly not the
end of the step of the loop's chain that takes `r` rounds (`StepMap`) from the start with forms `f`: one of the
step's identities for the right end, the left countdown and the width is decidedly false. -/
def stepMapNe (f : SForms) (r : Nat) (sW R' L' : YForm) : Bool :=
  if r = 8 then
    neDec ts Γ (R'.smul 16) f.R || neDec ts Γ (L'.smul 64) f.L || neDec ts Γ sW (f.E.addc 24)
  else if r = 2 then
    neDec ts Γ (R'.smul 2) f.R ||
      neDec ts Γ (L'.smul 2) (((f.L.add (f.E.smul 35)).sub (f.R.smul 147)).addc (-60)) ||
      neDec ts Γ sW (f.E.addc 6)
  else if r = 7 then
    neDec ts Γ (R'.smul 4704) ((((f.E.smul 476).add (f.R.smul 980)).sub f.L).addc 15984) ||
      neDec ts Γ (L'.smul 96) (((f.L.add (f.E.smul 1120)).add (f.R.smul 1666)).addc 50328) ||
      neDec ts Γ sW (f.E.addc 24)
  else true

theorem stepMapNe_sound {y : List Int} (hy : inCone ts Γ y) {f : SForms} {E R : Nat} {L : Int} (hf : f.Ag y E R L)
    {r : Nat} {sW R' L' : YForm} {W R'v : Nat} (hW : agN y sW W) (hR' : agN y R' R'v)
    (h : stepMapNe ts Γ f r sW R' L' = true) (k : StepKind) : ¬ StepMap k r E R L W R'v (L'.eval y) := by
  obtain ⟨hE, hR, hL⟩ := hf
  unfold agN at hE hR hW hR'
  cases k with
  | full =>
    rintro ⟨rfl, e1, e2, e3⟩
    simp only [stepMapNe, ↓reduceIte, Bool.or_eq_true] at h
    rcases h with (h | h) | h <;> have := neDec_sound ts Γ hy h <;> simp only [eval_smul, eval_addc] at this <;> omega
  | half =>
    rintro ⟨rfl, e1, e2, e3, -⟩
    simp only [stepMapNe, show (2 : Nat) ≠ 8 by decide, ↓reduceIte, Bool.or_eq_true] at h
    rcases h with (h | h) | h <;> have := neDec_sound ts Γ hy h <;>
      simp only [eval_smul, eval_addc, eval_add, eval_sub] at this <;> omega
  | break7 =>
    rintro ⟨rfl, e1, e2, e3⟩
    simp only [stepMapNe, show (7 : Nat) ≠ 8 by decide, show (7 : Nat) ≠ 2 by decide, ↓reduceIte,
      Bool.or_eq_true] at h
    rcases h with (h | h) | h <;> have := neDec_sound ts Γ hy h <;>
      simp only [eval_smul, eval_addc, eval_add, eval_sub] at this <;> omega

/-- The round start after `r` rounds is decidedly not a landing of the loop's chain (`Landing`) from the start with
forms `f`: it is not three walls, or the map of the step that takes `r` rounds decidedly fails on it. -/
def notLandingCheck (f : SForms) (r : Nat) (ss : List SMark) (sW : YForm) : Bool :=
  match swwwOf ss with
  | none => true
  | some (_, b, c) => stepMapNe ts Γ f r sW ((sW.sub c).addc (-1)) (L1Form b c sW)

theorem notLandingCheck_sound {y : List Int} (hy : inCone ts Γ y) {f : SForms} {E R : Nat} {L : Int}
    (hf : f.Ag y E R L) {r : Nat} {ss : List SMark} {sW : YForm} {ms : List Mark} {W : Nat} (hs : agL y ss ms)
    (hW : agN y sW W) (h : notLandingCheck ts Γ f r ss sW = true) : ¬ Landing r E R L ms W := by
  rintro ⟨k, a, b, c, R', rfl, -, -, -, hc, -, -, hS, -⟩
  have hag := wwwOf_agree hs
  unfold notLandingCheck at h
  cases hsw : swwwOf ss with
  | none =>
    have := hag.1 hsw
    simp [wwwOf] at this
  | some fs =>
    obtain ⟨fa, fb, fc⟩ := fs
    rw [hsw] at h
    obtain ⟨a', b', c', he, -, h2, h3⟩ := hag.2 fa fb fc hsw
    simp only [List.cons.injEq, Mark.mk.injEq, true_and, and_true] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    have hR'ag : agN y ((sW.sub fc).addc (-1)) R' := by
      unfold agN at h3 hW ⊢; simp only [eval_addc, eval_sub]; omega
    have hL' : loopL1 b c W = (L1Form fb fc sW).eval y := by
      unfold agN at h2 h3 hW
      rw [eval_L1Form, ← h2, ← h3, ← hW]; simp only [loopL1]
    rw [hL'] at hS
    exact stepMapNe_sound ts Γ hy hf hW hR'ag h k hS

/-- Marks of these types are a lone marker. -/
def loneMarker : List MarkT → Bool
  | [.M] => true
  | _ => false

/-- The model's outcome after `r` rounds is a round start that is decidedly no checkpoint of `pass_next` from the
start with forms `f`: not a lone marker, and either not three walls after 2, 7 or 8 rounds or decidedly not a landing
(`notLandingCheck`). -/
def symNoCheckpoint (f : SForms) (r : Nat) : SPR → Bool
  | .newRound ss sW => !loneMarker (ss.map (·.t)) &&
      (!typesMayCheckpoint r (ss.map (·.t)) || notLandingCheck ts Γ f r ss sW)
  | _ => false

/-- The model's rounds on a class, as `symOpenRun`, from a start with forms `f` (its width, right end and left
countdown): no round start before round N is a checkpoint of `pass_next` (`symNoCheckpoint`), and round N is left
uncovered. -/
def symOpenRun2 (f : SForms) (N : Nat) (ss : List SMark) (sW : YForm) : Bool :=
  (List.range N).all (fun r => match symRoundsZ ts Γ 1000 r ss sW with
    | some sr => symNoCheckpoint ts Γ f r sr
    | none => false) &&
  match symRoundsZ ts Γ 1000 N ss sW with
  | some .uncovered => true
  | _ => false

theorem symOpenRun2_sound {f : SForms} {N : Nat} {ss : List SMark} {sW : YForm}
    (h : symOpenRun2 ts Γ f N ss sW = true) {y : List Int} (hy : inCone ts Γ y) {E R : Nat} {L : Int}
    (hf : f.Ag y E R L) {ms : List Mark} {W : Nat} (hs : agL y ss ms) (hW : agN y sW W) :
    roundsZ 1000 N ms W = .uncovered ∧ ∀ r < N, ∀ ms' W', roundsZ 1000 r ms W = .newRound ms' W' →
      ¬ Landing r E R L ms' W' ∧ ¬ CleanTape ms' W' := by
  simp only [symOpenRun2, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨hc, hN⟩ := h
  constructor
  · cases e : symRoundsZ ts Γ 1000 N ss sW with
    | none => rw [e] at hN; cases hN
    | some sr =>
      have hag := symRoundsZ_sound ts Γ hy 1000 N ss ms sW W sr hs hW e
      rw [e] at hN
      cases sr with
      | uncovered =>
        generalize roundsZ 1000 N ms W = cr at hag ⊢
        cases cr with
        | uncovered => rfl
        | _ => exact absurd hag id
      | _ => cases hN
  · intro r hr ms' W' hrm
    have hcr := hc r hr
    cases e : symRoundsZ ts Γ 1000 r ss sW with
    | none => rw [e] at hcr; cases hcr
    | some sr =>
      have hag := symRoundsZ_sound ts Γ hy 1000 r ss ms sW W sr hs hW e
      rw [e] at hcr
      rw [hrm] at hag
      cases sr with
      | newRound ss' sW' =>
        obtain ⟨hs', hW'⟩ := hag
        have ht := agL_types hs'
        simp only [symNoCheckpoint, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hcr
        obtain ⟨hM, hcr⟩ := hcr
        refine ⟨fun hl => ?_, fun hcl => ?_⟩
        · rcases hcr with hcr | hcr
          · have := mayCheckpoint_of (R := R) (W := E) (Or.inl hl)
            simp only [mayCheckpoint, ← ht, hcr] at this
            cases this
          · exact notLandingCheck_sound ts Γ hy hf hs' hW' hcr hl
        · rw [hcl] at ht
          rw [ht] at hM
          simp [loneMarker] at hM
      | _ => exact absurd hag id

end

/-! ## The family -/

/-- The family: walls at a = 2 z₀ + 1, b = 2,010 + 2¹⁴ z₁ and b + 467, width b + 646 (R = 178), with the cone gaps a
and b − a. -/
def famStart : List SMark × YForm × List YForm :=
  let a : YForm := ⟨1, [2, 0]⟩
  let b : YForm := ⟨2010, [0, 16384]⟩
  let W : YForm := ⟨2656, [0, 16384]⟩
  ([⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W.addc (-179)⟩], W, [a, b.sub a])

/-- The close run closes the family. -/
theorem famStart_close :
    symCloseRun famStart.2.2 448 closeFuel [] (YForm.const 1) famStart.1 famStart.2.1 = true := by
  decide +kernel

/-- The model's run on the family: 18 round starts, none of which might be a checkpoint, then a round left
uncovered. -/
theorem famStart_open : symOpenRun famStart.2.2 448 19 famStart.1 famStart.2.1 = true := by
  decide +kernel

/-- **The family halts, open at every depth**: every pass start with walls at a, b and b + 467 and width b + 646
(R = 178), a odd, a ≥ 448, b − a ≥ 448 and b ≡ 2,010 (mod 2¹⁴), has every gap at least 448, lies in a cut leaf of
`passTreeSym` at every depth, and halts. -/
theorem family_open_halt {a b W : Nat} (ha : a % 2 = 1) (h1 : 448 ≤ a) (h2 : a + 448 ≤ b) (hb : b % 16384 = 2010)
    (hW : W = b + 646) :
    PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - 178 - 1⟩] W 178 ∧
    (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W : Int) / 2, 89] = true) ∧
    ∃ T, steps T (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - 178 - 1⟩] W) = none := by
  subst hW
  have hP : PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, b + 646 - 178 - 1⟩] (b + 646) 178 :=
    ⟨a, b, rfl, ha, by omega, by omega, rfl, by omega, h1, h2, by omega⟩
  let y : List Int := [((a : Int) - 1) / 2, ((b : Int) - 2010) / 16384]
  have hy : inCone famStart.2.2 448 y := by
    intro f hf
    simp only [famStart, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl
    · simp only [y, YForm.eval, dot]; omega
    · simp only [eval_sub]; simp only [y, YForm.eval, dot]; omega
  have hs : agL y famStart.1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, b + 646 - 178 - 1⟩] := by
    refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, trivial⟩ <;> simp only [agN, eval_addc] <;>
      simp only [y, YForm.eval, dot] <;> omega
  have hWa : agN y famStart.2.1 (b + 646) := by
    simp only [y, agN, famStart, YForm.eval, dot]; omega
  obtain ⟨hN, hc⟩ := symOpenRun_sound famStart_open hy hs hWa
  obtain ⟨hwf, hG⟩ := hP.wf
  exact ⟨hP, sym_open_of_run (Nat.le_refl _) hP hN hc, symCloseRun_halt _ _ closeFuel famStart_close hy hs hWa hwf hG⟩

/-! ## More families -/

/-- A family of pass starts with right end R₀: the first wall a anywhere (odd, at least 448 and at least 448 before the
second), the second at b = b₀ + 2^k t, the third at b + (W₀ − R₀ − 1 − b₀) and the width b + (W₀ − b₀); the model's run
on it leaves round N uncovered. -/
structure Fam where
  W0 : Nat
  R0 : Nat
  b0 : Nat
  k : Nat
  N : Nat

/-- The family as a class: a = 2 y₀ + 1, b = b₀ + 2^k y₁ and W = W₀ + 2^k y₁, with the cone gaps a and b − a. -/
def Fam.start (F : Fam) : List SMark × YForm × List YForm :=
  let a : YForm := ⟨1, [2, 0]⟩
  let b : YForm := ⟨(F.b0 : Int), [0, 2 ^ F.k]⟩
  let W : YForm := ⟨(F.W0 : Int), [0, 2 ^ F.k]⟩
  ([⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W.addc (-(F.R0 : Int) - 1)⟩], W, [a, b.sub a])

/-- The family's width, right end and left countdown as forms. -/
def Fam.forms (F : Fam) : SForms :=
  let b : YForm := ⟨(F.b0 : Int), [0, 2 ^ F.k]⟩
  let W : YForm := ⟨(F.W0 : Int), [0, 2 ^ F.k]⟩
  ⟨W, YForm.const F.R0, L1Form b (W.addc (-(F.R0 : Int) - 1)) W⟩

/-- The checks on a family: the parities, R₀ ≥ 178, a third gap of at least 448, and the close run and the model's
run (`symOpenRun2`, N rounds) on the class. -/
def Fam.ok (F : Fam) : Bool :=
  F.b0 % 2 == 0 && F.W0 % 2 == 0 && F.R0 % 2 == 0 && 178 ≤ F.R0 && 1 ≤ F.k && F.b0 + 448 + F.R0 + 1 ≤ F.W0 &&
  symCloseRun F.start.2.2 448 closeFuel [] (YForm.const 1) F.start.1 F.start.2.1 &&
  symOpenRun2 F.start.2.2 448 F.forms F.N F.start.1 F.start.2.1

/-- A member of a family, with its first wall at a and its second at b₀ + 2^k t, agrees with the family's class at
y = [(a − 1)/2, t]. -/
theorem Fam.ag {F : Fam} (hg : F.b0 + 448 + F.R0 + 1 ≤ F.W0) {a t : Nat} (ha : a % 2 = 1) (h1 : 448 ≤ a)
    (h2 : a + 448 ≤ F.b0 + 2 ^ F.k * t) :
    inCone F.start.2.2 448 [((a : Int) - 1) / 2, (t : Int)] ∧
    agL [((a : Int) - 1) / 2, (t : Int)] F.start.1
      [⟨.W, a⟩, ⟨.W, F.b0 + 2 ^ F.k * t⟩, ⟨.W, F.W0 + 2 ^ F.k * t - F.R0 - 1⟩] ∧
    agN [((a : Int) - 1) / 2, (t : Int)] F.start.2.1 (F.W0 + 2 ^ F.k * t) := by
  have hXI : (2 : Int) ^ F.k * (t : Int) = ((2 ^ F.k * t : Nat) : Int) := by
    rw [Int.natCast_mul, Int.natCast_pow]; rfl
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    simp only [Fam.start, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl
    · simp only [YForm.eval, dot]; omega
    · simp only [eval_sub]; simp only [YForm.eval, dot]; rw [hXI]; omega
  · refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, trivial⟩ <;> simp only [agN, eval_addc] <;>
      simp only [YForm.eval, dot] <;> (try rw [hXI]) <;> omega
  · simp only [agN, Fam.start, YForm.eval, dot]; rw [hXI]; omega

/-- **A family that passes the checks halts, open at every depth**, as `family_open_halt`: every member is a pass
start with every gap at least 448 that lies in a cut leaf of `passTreeSym` at every depth, and the machine halts from
it. -/
theorem Fam.open_halt {F : Fam} (hF : F.ok = true) {a t : Nat} (ha : a % 2 = 1) (h1 : 448 ≤ a)
    (h2 : a + 448 ≤ F.b0 + 2 ^ F.k * t) :
    PassStart448 [⟨.W, a⟩, ⟨.W, F.b0 + 2 ^ F.k * t⟩, ⟨.W, F.W0 + 2 ^ F.k * t - F.R0 - 1⟩] (F.W0 + 2 ^ F.k * t)
      F.R0 ∧
    (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, ((F.b0 + 2 ^ F.k * t : Nat) : Int) / 2,
      ((F.W0 + 2 ^ F.k * t : Nat) : Int) / 2, (F.R0 : Int) / 2] = true) ∧
    ∃ T, steps T (roundStart [⟨.W, a⟩, ⟨.W, F.b0 + 2 ^ F.k * t⟩, ⟨.W, F.W0 + 2 ^ F.k * t - F.R0 - 1⟩]
      (F.W0 + 2 ^ F.k * t)) = none := by
  simp only [Fam.ok, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hF
  obtain ⟨⟨⟨⟨⟨⟨⟨hb0, hW0⟩, hR0⟩, h178⟩, hk⟩, hg⟩, hcl⟩, hop⟩ := hF
  have hX2 : (2 ^ F.k * t) % 2 = 0 := by
    obtain ⟨j, hj⟩ : ∃ j, F.k = j + 1 := ⟨F.k - 1, by omega⟩
    rw [hj, Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, Nat.mul_assoc, Nat.mul_mod_right]
  have hXI : (2 : Int) ^ F.k * (t : Int) = ((2 ^ F.k * t : Nat) : Int) := by
    rw [Int.natCast_mul, Int.natCast_pow]; rfl
  let y : List Int := [((a : Int) - 1) / 2, (t : Int)]
  obtain ⟨hy, hs, hWa⟩ := Fam.ag hg ha h1 h2
  have hP : PassStart448 [⟨.W, a⟩, ⟨.W, F.b0 + 2 ^ F.k * t⟩, ⟨.W, F.W0 + 2 ^ F.k * t - F.R0 - 1⟩]
      (F.W0 + 2 ^ F.k * t) F.R0 :=
    ⟨a, F.b0 + 2 ^ F.k * t, rfl, ha, by omega, by omega, hR0, by omega, h1, h2, by omega⟩
  have hf : F.forms.Ag y (F.W0 + 2 ^ F.k * t) F.R0
      (passL1 [⟨.W, a⟩, ⟨.W, F.b0 + 2 ^ F.k * t⟩, ⟨.W, F.W0 + 2 ^ F.k * t - F.R0 - 1⟩] (F.W0 + 2 ^ F.k * t)) := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [y, agN, Fam.forms, YForm.eval, dot]; rw [hXI]; omega
    · simp only [agN, Fam.forms, eval_const]
    · simp only [passL1, loopL1, Fam.forms, eval_L1Form, eval_addc]
      simp only [y, YForm.eval, dot]; rw [hXI]; omega
  obtain ⟨hN, hc⟩ := symOpenRun2_sound _ _ hop hy hf hs hWa
  obtain ⟨hwf, hG⟩ := hP.wf
  exact ⟨hP, sym_open_of_run2 h178 hP hN hc, symCloseRun_halt _ _ closeFuel hcl hy hs hWa hwf hG⟩

/-- The families, as (W₀, R₀, b₀, k, N): the seven of the eleven closing placements with R ≥ 178 and width from 2,048 to
3,072 (an untrusted scan, three first walls for each placement of the other walls) that repeat this way, and one at
width 13,400 that a full pass of the loop's chain lands on (`full_pass_open_halt`).  The fourth is the family of
`family_open_halt`. -/
def openHaltFams : List Fam :=
  [⟨2368, 466, 1274, 15, 21⟩, ⟨2376, 402, 956, 14, 21⟩, ⟨2460, 578, 1304, 14, 21⟩, ⟨2656, 178, 2010, 14, 19⟩,
   ⟨2760, 914, 1084, 15, 24⟩, ⟨2872, 474, 1794, 15, 21⟩, ⟨2962, 210, 2288, 13, 18⟩, ⟨13400, 186, 9698, 17, 22⟩]

/-- All eight pass the checks (the close run and the model's run on each, by the kernel). -/
theorem openHaltFams_ok : openHaltFams.all Fam.ok = true := by decide +kernel

/-- **Eight families of pass starts with R ≥ 178 that halt, open at every depth, at every width.** -/
theorem open_halt_families {F : Fam} (hF : F ∈ openHaltFams) {a t : Nat} (ha : a % 2 = 1) (h1 : 448 ≤ a)
    (h2 : a + 448 ≤ F.b0 + 2 ^ F.k * t) :
    PassStart448 [⟨.W, a⟩, ⟨.W, F.b0 + 2 ^ F.k * t⟩, ⟨.W, F.W0 + 2 ^ F.k * t - F.R0 - 1⟩] (F.W0 + 2 ^ F.k * t)
      F.R0 ∧
    (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, ((F.b0 + 2 ^ F.k * t : Nat) : Int) / 2,
      ((F.W0 + 2 ^ F.k * t : Nat) : Int) / 2, (F.R0 : Int) / 2] = true) ∧
    ∃ T, steps T (roundStart [⟨.W, a⟩, ⟨.W, F.b0 + 2 ^ F.k * t⟩, ⟨.W, F.W0 + 2 ^ F.k * t - F.R0 - 1⟩]
      (F.W0 + 2 ^ F.k * t)) = none :=
  Fam.open_halt (List.all_eq_true.1 openHaltFams_ok F hF) ha h1 h2

/-! ## A full pass onto one -/

/-- The mark lists are equal (types and positions compared). -/
def marksEq : List Mark → List Mark → Bool
  | [], [] => true
  | m :: ms, m' :: ms' => m.t == m'.t && m.p == m'.p && marksEq ms ms'
  | _, _ => false

theorem marksEq_eq : ∀ {ms ms' : List Mark}, marksEq ms ms' = true → ms = ms'
  | [], [], _ => rfl
  | ⟨t, p⟩ :: ms, ⟨t', p'⟩ :: ms', h => by
    simp only [marksEq, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, rfl⟩, h⟩ := h
    rw [marksEq_eq h]
  | [], _ :: _, h => by simp [marksEq] at h
  | _ :: _, [], h => by simp [marksEq] at h

/-- The model's outcome is the round start `ms`, `W`. -/
def isRoundAt : PR' → List Mark → Nat → Bool
  | .newRound ms' W', ms, W => W' == W && marksEq ms' ms
  | _, _, _ => false

theorem isRoundAt_eq {r : PR'} {ms : List Mark} {W : Nat} (h : isRoundAt r ms W = true) : r = .newRound ms W := by
  cases r with
  | newRound ms' W' =>
    simp only [isRoundAt, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, marksEq_eq h.2]
  | _ => simp [isRoundAt] at h

/-- The full pass: eight rounds from walls at 449, 1,182 and 10,399, width 13,376 (R = 2,976), to walls at 3,187,
9,698 and 13,213, width 13,400 (R = 186). -/
theorem full_pass_land : isRoundAt (roundsZ 1000 8 [⟨.W, 449⟩, ⟨.W, 1182⟩, ⟨.W, 10399⟩] 13376)
    [⟨.W, 3187⟩, ⟨.W, 9698⟩, ⟨.W, 13213⟩] 13400 = true := by decide +kernel

/-- Its end meetings are all at distance at least 3. -/
theorem full_pass_meets : ∀ d ∈ meetsRounds 1000 8 [⟨.W, 449⟩, ⟨.W, 1182⟩, ⟨.W, 10399⟩] 13376, 3 ≤ d := by
  decide +kernel

/-- **The loop's chain can end at such a pass start after a full pass.**  The pass start with walls at 449, 1,182 and
10,399 and width 13,376 (R = 2,976 = 16 · 186, left countdown −157,952 = 64 · (−2,468)) makes a full pass of the loop
(`LoopChain` with one step of kind `full`) and lands at walls 3,187, 9,698 and 13,213, width 13,400 (R = 186, a member
of the eighth family), which `passTreeSym` leaves open at every depth and from which the machine halts: the end is
met at 184 = R − 2, then at 1,022 = 2¹⁰ − 2 off the chain, whose halving chain runs to the close in round 22. -/
theorem full_pass_open_halt :
    LoopChain [⟨.W, 449⟩, ⟨.W, 1182⟩, ⟨.W, 10399⟩] 13376 2976 [.full] [⟨.W, 3187⟩, ⟨.W, 9698⟩, ⟨.W, 13213⟩] 13400
      186 ∧
    (∀ d, (passTreeSym d).cutMem [1593, 4849, 6700, 93] = true) ∧
    ∃ T, steps T (roundStart [⟨.W, 3187⟩, ⟨.W, 9698⟩, ⟨.W, 13213⟩] 13400) = none := by
  have hF : Fam.ok ⟨13400, 186, 9698, 17, 22⟩ = true := by decide +kernel
  obtain ⟨hP₁, hcut, hT⟩ := Fam.open_halt hF (a := 3187) (t := 0) (by decide) (by decide) (by decide)
  have hP₀ : PassStart448 [⟨.W, 449⟩, ⟨.W, 1182⟩, ⟨.W, 10399⟩] 13376 2976 :=
    ⟨449, 1182, rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  have hr := isRoundAt_eq full_pass_land
  obtain ⟨kk, hk, -⟩ := rounds_run 1000 8 _ _ hP₀.wf.1 (by rw [hr]; intro h; cases h)
  rw [hr] at hk
  exact ⟨.cons .full 8 kk hP₀ hk hr full_pass_meets (by decide) ⟨rfl, rfl, by decide, rfl⟩ (.nil hP₁), hcut, hT⟩

/-! ## The same route at larger scales -/

/-- One family at each scale j from 10 to 30, all with R = 178 and W − b = 2^(j+2) − 2R − 22, as (W₀, R₀, b₀, k, N).
On this route the end is met at R − 2, then off the chain at (W − b + 2R + 14)/4 = 2^j − 2, and that meeting's
halving chain runs to the close.  The class of b modulo 2^k (k about 1.5 j + 2) is the one an untrusted symbolic search
of the model's rounds finds for that j and R. -/
def reentryFams : List Fam :=
  [⟨12896, 178, 9178, 17, 22⟩, ⟨201312, 178, 193498, 19, 24⟩, ⟨840288, 178, 824282, 20, 27⟩,
   ⟨1069664, 178, 1037274, 21, 29⟩, ⟨5722720, 178, 5657562, 23, 30⟩, ⟨6640224, 178, 6509530, 25, 32⟩,
   ⟨42029664, 178, 41767898, 26, 35⟩, ⟨45699680, 178, 45175770, 27, 37⟩, ⟨321475168, 178, 320426970, 29, 38⟩,
   ⟨336155232, 178, 334058458, 31, 40⟩, ⟨2512999008, 178, 2508805082, 32, 43⟩, ⟨2571719264, 178, 2563331034, 33, 45⟩,
   ⟨19869028960, 178, 19852252122, 35, 46⟩, ⟨20103909984, 178, 20070355930, 37, 48⟩,
   ⟨158012625504, 178, 157945517018, 38, 51⟩, ⟨158952149600, 178, 158817932250, 39, 53⟩,
   ⟨1260342825568, 178, 1260074390490, 41, 54⟩, ⟨1264100921952, 178, 1263564051418, 43, 56⟩,
   ⟨10067710136928, 178, 10066636395482, 44, 59⟩, ⟨10082742522464, 178, 10080595039194, 45, 61⟩,
   ⟨80481551471200, 178, 80477256504282, 47, 62⟩]

/-- The j-th has R = 178 and W − b = 2^(j+2) − 378. -/
theorem reentryFams_shape :
    reentryFams.map (fun F => (F.R0, F.W0 - F.b0)) = (List.range 21).map (fun i => (178, 2 ^ (i + 12) - 378)) := by
  decide +kernel

/-- All 21 pass the checks (the close run and the model's run on each, by the kernel). -/
theorem reentryFams_ok : reentryFams.all Fam.ok = true := by decide +kernel

/-- **At each scale j from 10 to 30, a family of pass starts with R = 178 and W − b = 2^(j+2) − 378 that halt, open
at every depth, at every width.** -/
theorem reentry_open_halt {F : Fam} (hF : F ∈ reentryFams) {a t : Nat} (ha : a % 2 = 1) (h1 : 448 ≤ a)
    (h2 : a + 448 ≤ F.b0 + 2 ^ F.k * t) :
    PassStart448 [⟨.W, a⟩, ⟨.W, F.b0 + 2 ^ F.k * t⟩, ⟨.W, F.W0 + 2 ^ F.k * t - F.R0 - 1⟩] (F.W0 + 2 ^ F.k * t)
      F.R0 ∧
    (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, ((F.b0 + 2 ^ F.k * t : Nat) : Int) / 2,
      ((F.W0 + 2 ^ F.k * t : Nat) : Int) / 2, (F.R0 : Int) / 2] = true) ∧
    ∃ T, steps T (roundStart [⟨.W, a⟩, ⟨.W, F.b0 + 2 ^ F.k * t⟩, ⟨.W, F.W0 + 2 ^ F.k * t - F.R0 - 1⟩]
      (F.W0 + 2 ^ F.k * t)) = none :=
  Fam.open_halt (List.all_eq_true.1 reentryFams_ok F hF) ha h1 h2

/-! ## With R ≡ 6 (mod 8) -/

/-- One family at each scale j from 10 to 30, all with R = 182 and W − b = 2^(j+2) − 2R − 22, as (W₀, R₀, b₀, k, N):
the class of b modulo 2^k that the untrusted search finds for that j and R.  The run passes three-wall round starts
in rounds 5 and 7 (the second the half pass of the first, with right end 2^(j−2)), which are no landings. -/
def reentryFams6 : List Fam :=
  [⟨102316, 182, 98606, 17, 23⟩, ⟨90028, 182, 82222, 18, 25⟩, ⟨589740, 182, 573742, 20, 26⟩,
   ⟨3162028, 182, 3129646, 22, 28⟩, ⟨4112300, 182, 4047150, 23, 31⟩, ⟨6012844, 182, 5882158, 24, 33⟩,
   ⟨43368364, 182, 43106606, 26, 34⟩, ⟨17416108, 182, 16892206, 28, 36⟩, ⟨99729324, 182, 98681134, 29, 39⟩,
   ⟨801226668, 182, 799129902, 30, 41⟩, ⟨1130479532, 182, 1126285614, 32, 42⟩,
   ⟨10378919852, 182, 10370531630, 34, 44⟩, ⟨11695931308, 182, 11679154478, 35, 47⟩,
   ⟨14329954220, 182, 14296400174, 36, 49⟩, ⟨157036953516, 182, 156969845038, 38, 50⟩,
   ⟨579889905580, 182, 579755688238, 40, 52⟩, ⟨1425595809708, 182, 1425327374638, 41, 55⟩,
   ⟨917984362412, 182, 917447491886, 42, 57⟩, ⟨8698854490028, 182, 8697780748590, 44, 58⟩,
   ⟨15464501723052, 182, 15462354239790, 46, 60⟩, ⟨134548912455596, 182, 134544617488686, 47, 63⟩]

/-- The j-th has R = 182 and W − b = 2^(j+2) − 386. -/
theorem reentryFams6_shape :
    reentryFams6.map (fun F => (F.R0, F.W0 - F.b0)) = (List.range 21).map (fun i => (182, 2 ^ (i + 12) - 386)) := by
  decide +kernel

/-- All 21 pass the checks (the close run and the model's run on each, by the kernel). -/
theorem reentryFams6_ok : reentryFams6.all Fam.ok = true := by decide +kernel

/-- **At each scale j from 10 to 30, a family of pass starts with R = 182 and W − b = 2^(j+2) − 386 that halt, open
at every depth, at every width.** -/
theorem reentry6_open_halt {F : Fam} (hF : F ∈ reentryFams6) {a t : Nat} (ha : a % 2 = 1) (h1 : 448 ≤ a)
    (h2 : a + 448 ≤ F.b0 + 2 ^ F.k * t) :
    PassStart448 [⟨.W, a⟩, ⟨.W, F.b0 + 2 ^ F.k * t⟩, ⟨.W, F.W0 + 2 ^ F.k * t - F.R0 - 1⟩] (F.W0 + 2 ^ F.k * t)
      F.R0 ∧
    (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, ((F.b0 + 2 ^ F.k * t : Nat) : Int) / 2,
      ((F.W0 + 2 ^ F.k * t : Nat) : Int) / 2, (F.R0 : Int) / 2] = true) ∧
    ∃ T, steps T (roundStart [⟨.W, a⟩, ⟨.W, F.b0 + 2 ^ F.k * t⟩, ⟨.W, F.W0 + 2 ^ F.k * t - F.R0 - 1⟩]
      (F.W0 + 2 ^ F.k * t)) = none :=
  Fam.open_halt (List.all_eq_true.1 reentryFams6_ok F hF) ha h1 h2

/-- The full pass: eight rounds from walls at 449, 4,318 and 25,827, width 29,380 (R = 3,552), to walls at 7,201,
21,678 and 29,181, width 29,404 (R = 222). -/
theorem full_pass_land6 : isRoundAt (roundsZ 1000 8 [⟨.W, 449⟩, ⟨.W, 4318⟩, ⟨.W, 25827⟩] 29380)
    [⟨.W, 7201⟩, ⟨.W, 21678⟩, ⟨.W, 29181⟩] 29404 = true := by decide +kernel

/-- Its end meetings are all at distance at least 3. -/
theorem full_pass_meets6 : ∀ d ∈ meetsRounds 1000 8 [⟨.W, 449⟩, ⟨.W, 4318⟩, ⟨.W, 25827⟩] 29380, 3 ≤ d := by
  decide +kernel

/-- **The loop's chain can end after a full pass at such a pass start with R ≡ 6 (mod 8).**  The pass start with walls
at 449, 4,318 and 25,827 and width 29,380 (R = 3,552 = 16 · 222, left countdown −1,263,616 = 64 · (−19,744)) makes a
full pass of the loop and lands at walls 7,201, 21,678 and 29,181, width 29,404 (R = 222, in the class of the scale
j = 11: W − b = 7,726 = 2¹³ − 2R − 22), which `passTreeSym` leaves open at every depth and from which the machine
halts. -/
theorem full_pass_open_halt6 :
    LoopChain [⟨.W, 449⟩, ⟨.W, 4318⟩, ⟨.W, 25827⟩] 29380 3552 [.full] [⟨.W, 7201⟩, ⟨.W, 21678⟩, ⟨.W, 29181⟩] 29404
      222 ∧
    (∀ d, (passTreeSym d).cutMem [3600, 10839, 14702, 111] = true) ∧
    ∃ T, steps T (roundStart [⟨.W, 7201⟩, ⟨.W, 21678⟩, ⟨.W, 29181⟩] 29404) = none := by
  have hF : Fam.ok ⟨29404, 222, 21678, 18, 25⟩ = true := by decide +kernel
  obtain ⟨hP₁, hcut, hT⟩ := Fam.open_halt hF (a := 7201) (t := 0) (by decide) (by decide) (by decide)
  have hP₀ : PassStart448 [⟨.W, 449⟩, ⟨.W, 4318⟩, ⟨.W, 25827⟩] 29380 3552 :=
    ⟨449, 4318, rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  have hr := isRoundAt_eq full_pass_land6
  obtain ⟨kk, hk, -⟩ := rounds_run 1000 8 _ _ hP₀.wf.1 (by rw [hr]; intro h; cases h)
  rw [hr] at hk
  exact ⟨.cons .full 8 kk hP₀ hk hr full_pass_meets6 (by decide) ⟨rfl, rfl, by decide, rfl⟩ (.nil hP₁), hcut, hT⟩

/-! ## With no pass start on the way -/

/-- No round start of the model's run on the class after round 0 is three walls: none from round 1 to round N − 1,
and round N is left uncovered. -/
def symNoWWWRun (ts : List YForm) (Γ : Int) (N : Nat) (ss : List SMark) (sW : YForm) : Bool :=
  (List.range N).all (fun r => r == 0 || match symRoundsZ ts Γ 1000 r ss sW with
    | some (.newRound ss' _) => (swwwOf ss').isNone
    | _ => false) &&
  match symRoundsZ ts Γ 1000 N ss sW with
  | some .uncovered => true
  | _ => false

theorem symNoWWWRun_sound {ts : List YForm} {Γ : Int} {N : Nat} {ss : List SMark} {sW : YForm}
    (h : symNoWWWRun ts Γ N ss sW = true) {y : List Int} (hy : inCone ts Γ y) {ms : List Mark} {W : Nat}
    (hs : agL y ss ms) (hW : agN y sW W) {r : Nat} (hr0 : 0 < r) {ms' : List Mark} {W' : Nat}
    (hr : roundsZ 1000 r ms W = .newRound ms' W') : NotWWW ms' := by
  simp only [symNoWWWRun, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨hc, hN⟩ := h
  by_cases hrN : r < N
  · rcases hc r hrN with h | h
    · omega
    · cases e : symRoundsZ ts Γ 1000 r ss sW with
      | none => rw [e] at h; cases h
      | some sr =>
        have hag := symRoundsZ_sound ts Γ hy 1000 r ss ms sW W sr hs hW e
        rw [e] at h
        rw [hr] at hag
        cases sr with
        | newRound ss' sW' =>
          simp only [Option.isNone_iff_eq_none] at h
          exact notWWW_of_none hag.1 h
        | _ => exact absurd hag id
  · have hU : roundsZ 1000 N ms W = .uncovered := by
      cases e : symRoundsZ ts Γ 1000 N ss sW with
      | none => rw [e] at hN; cases hN
      | some sr =>
        have hag := symRoundsZ_sound ts Γ hy 1000 N ss ms sW W sr hs hW e
        rw [e] at hN
        cases sr with
        | uncovered =>
          generalize roundsZ 1000 N ms W = cr at hag ⊢
          cases cr with
          | uncovered => rfl
          | _ => exact absurd hag id
        | _ => cases hN
    have := roundsZ_uncovered_add 1000 N (r - N) ms W hU
    rw [show N + (r - N) = r by omega, hr] at this
    cases this

/-- Four families with R = 230, as (W₀, R₀, b₀, k, N): the classes of an untrusted census (every even R from 178 to
262, W − b up to 4,096 or 8,192) whose run reaches no three-wall round start after the first.  The run meets the end at
228 = R − 2, then at 510 = 2⁹ − 2 (W − b = 1,570) or 1,022 = 2¹⁰ − 2 (W − b = 3,618) off the loop's chain, and halves
from there, 254, 126, ..., 2, 0, to the close, through round starts with four walls or with a marker or a block. -/
def noPassFams : List Fam :=
  [⟨13504, 230, 11934, 15, 19⟩, ⟨29888, 230, 28318, 16, 22⟩, ⟨62656, 230, 61086, 16, 19⟩,
   ⟨36032, 230, 32414, 16, 21⟩]

/-- All four pass the checks, and on each no round start of the model's run after round 0 is three walls (by the
kernel). -/
theorem noPassFams_ok :
    noPassFams.all (fun F => F.ok && symNoWWWRun F.start.2.2 448 F.N F.start.1 F.start.2.1) = true := by
  decide +kernel

/-- **Four families of pass starts with R = 230 that halt, open at every depth, at every width, with no pass start
on the way**: as `open_halt_families`, and no round start of the model's run after round 0 is three walls, so the
run from such a pass start to the halt meets no other pass start, and no right end R′ or left countdown L₁′ of a
later one bounds the width. -/
theorem no_pass_open_halt {F : Fam} (hF : F ∈ noPassFams) {a t : Nat} (ha : a % 2 = 1) (h1 : 448 ≤ a)
    (h2 : a + 448 ≤ F.b0 + 2 ^ F.k * t) :
    PassStart448 [⟨.W, a⟩, ⟨.W, F.b0 + 2 ^ F.k * t⟩, ⟨.W, F.W0 + 2 ^ F.k * t - F.R0 - 1⟩] (F.W0 + 2 ^ F.k * t)
      F.R0 ∧
    (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, ((F.b0 + 2 ^ F.k * t : Nat) : Int) / 2,
      ((F.W0 + 2 ^ F.k * t : Nat) : Int) / 2, (F.R0 : Int) / 2] = true) ∧
    (∃ T, steps T (roundStart [⟨.W, a⟩, ⟨.W, F.b0 + 2 ^ F.k * t⟩, ⟨.W, F.W0 + 2 ^ F.k * t - F.R0 - 1⟩]
      (F.W0 + 2 ^ F.k * t)) = none) ∧
    ∀ r, 0 < r → ∀ ms' W', roundsZ 1000 r [⟨.W, a⟩, ⟨.W, F.b0 + 2 ^ F.k * t⟩,
      ⟨.W, F.W0 + 2 ^ F.k * t - F.R0 - 1⟩] (F.W0 + 2 ^ F.k * t) = .newRound ms' W' → NotWWW ms' := by
  have h := List.all_eq_true.1 noPassFams_ok F hF
  simp only [Bool.and_eq_true] at h
  obtain ⟨hok, hnw⟩ := h
  obtain ⟨hP, hcut, hT⟩ := Fam.open_halt hok ha h1 h2
  have hg : F.b0 + 448 + F.R0 + 1 ≤ F.W0 := by
    simp only [Fam.ok, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, hg⟩, -⟩, -⟩ := hok
    exact hg
  obtain ⟨hy, hs, hWa⟩ := Fam.ag hg ha h1 h2
  exact ⟨hP, hcut, hT, fun r hr0 ms' W' hr => symNoWWWRun_sound hnw hy hs hWa hr0 hr⟩

/-! ## Two lanes at R = 486, at every scale tried -/

/-- One family at each scale from Q = W − b + 2R + 22 = 2¹² − 636 to 2³⁰ − 636, all with R = 486 (so
W − b = 2^(12+s) − 1,630, s = 0 to 18), as (W₀, R₀, b₀, k, N): the class of b modulo 2^k that the untrusted search
finds on this lane at that scale.  The run meets the end at 484 = R − 2, then off the loop's chain at
Q/4 − 3 = 2^(10+s) − 162, and its end meetings follow the chain from there to 0.  Its first three-wall round start
after the first is in round 17, with width ≡ 2 (mod 4) and right end (Q + 636)/1,024; that start's half pass, in round
19, begins the full passes of the loop's chain to the close. -/
def lane486a : List Fam :=
  [⟨15168, 486, 12702, 16, 21⟩, ⟨60224, 486, 53662, 18, 22⟩, ⟨412480, 486, 397726, 20, 24⟩,
   ⟨592704, 486, 561566, 21, 27⟩, ⟨953152, 486, 889246, 22, 29⟩, ⟨5868352, 486, 5738910, 24, 30⟩,
   ⟨49253184, 486, 48992670, 26, 32⟩, ⟨35359552, 486, 34836894, 27, 35⟩, ⟨141790016, 486, 140743070, 28, 37⟩,
   ⟨623086400, 486, 620990878, 30, 38⟩, ⟨3733162816, 486, 3728970142, 32, 40⟩, ⟨7805832000, 486, 7797445022, 33, 43⟩,
   ⟨7361235776, 486, 7344460190, 34, 45⟩, ⟨6472043328, 486, 6438490526, 36, 46⟩,
   ⟨176492350272, 486, 176425243038, 38, 48⟩, ⟨241655057216, 486, 241520841118, 39, 51⟩,
   ⟨921736284992, 486, 921467851166, 40, 53⟩, ⟨82875484992, 486, 82338615710, 42, 54⟩,
   ⟨13798316673856, 486, 13797242933662, 44, 56⟩]

/-- The second lane, as `lane486a`: the first three-wall round start after the first is in round 13, with width ≡ 2
(mod 4) and right end (Q + 636)/256, and its half pass begins the full passes to the close. -/
def lane486b : List Fam :=
  [⟨34624, 486, 32158, 15, 20⟩, ⟨30528, 486, 23966, 16, 23⟩, ⟨22336, 486, 7582, 17, 25⟩,
   ⟨137024, 486, 105886, 19, 26⟩, ⟨890688, 486, 826782, 21, 28⟩, ⟨3446592, 486, 3317150, 22, 31⟩,
   ⟨4364096, 486, 4103582, 23, 33⟩, ⟨31364928, 486, 30842270, 25, 34⟩, ⟨102143808, 486, 101096862, 27, 36⟩,
   ⟨176592704, 486, 174497182, 28, 39⟩, ⟨325490496, 486, 321297822, 29, 41⟩, ⟨1160156992, 486, 1151770014, 31, 42⟩,
   ⟨1755748160, 486, 1738972574, 33, 44⟩, ⟨11536865088, 486, 11503312286, 34, 47⟩,
   ⟨31099098944, 486, 31031991710, 35, 49⟩, ⟨104583305024, 486, 104449088926, 37, 50⟩,
   ⟨251551717184, 486, 251283283358, 39, 52⟩, ⟨270610634560, 486, 270073765278, 40, 55⟩,
   ⟨1408240097088, 486, 1407166356894, 41, 57⟩]

/-- The s-th of each lane has R = 486 and W − b = 2^(12+s) − 1,630. -/
theorem lane486_shape :
    lane486a.map (fun F => (F.R0, F.W0 - F.b0)) = (List.range 19).map (fun i => (486, 2 ^ (i + 12) - 1630)) ∧
    lane486b.map (fun F => (F.R0, F.W0 - F.b0)) = (List.range 19).map (fun i => (486, 2 ^ (i + 12) - 1630)) := by
  decide +kernel

/-- All 38 pass the checks (the close run and the model's run on each, by the kernel). -/
theorem lane486_ok : (lane486a ++ lane486b).all Fam.ok = true := by decide +kernel

/-- **At each scale W − b = 2^(12+s) − 1,630 from s = 0 to 18, two families of pass starts with R = 486 that halt,
open at every depth, at every width.** -/
theorem lane486_open_halt {F : Fam} (hF : F ∈ lane486a ++ lane486b) {a t : Nat} (ha : a % 2 = 1) (h1 : 448 ≤ a)
    (h2 : a + 448 ≤ F.b0 + 2 ^ F.k * t) :
    PassStart448 [⟨.W, a⟩, ⟨.W, F.b0 + 2 ^ F.k * t⟩, ⟨.W, F.W0 + 2 ^ F.k * t - F.R0 - 1⟩] (F.W0 + 2 ^ F.k * t)
      F.R0 ∧
    (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, ((F.b0 + 2 ^ F.k * t : Nat) : Int) / 2,
      ((F.W0 + 2 ^ F.k * t : Nat) : Int) / 2, (F.R0 : Int) / 2] = true) ∧
    ∃ T, steps T (roundStart [⟨.W, a⟩, ⟨.W, F.b0 + 2 ^ F.k * t⟩, ⟨.W, F.W0 + 2 ^ F.k * t - F.R0 - 1⟩]
      (F.W0 + 2 ^ F.k * t)) = none :=
  Fam.open_halt (List.all_eq_true.1 lane486_ok F hF) ha h1 h2

/-! ## At every width -/

/-- **Pass starts with R ≥ 178 that halt and that `passTreeSym` leaves open at every depth, at every width.** -/
theorem sym_open_halt (N : Nat) : ∃ R a b W, N < W ∧ 178 ≤ R ∧ PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R ∧
    (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W : Int) / 2, (R : Int) / 2] = true) ∧
    ∃ T, steps T (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = none := by
  obtain ⟨hP, hcut, hT⟩ := family_open_halt (a := 449) (b := 2010 + 16384 * N) (W := 2010 + 16384 * N + 646) rfl
    (by omega) (by omega) (by omega) rfl
  exact ⟨178, 449, 2010 + 16384 * N, 2010 + 16384 * N + 646, by omega, Nat.le_refl _, hP, hcut, hT⟩

/-- One wider than the clean tapes of `never_halts_of_open`: the pass start alone does not answer its second
question. -/
theorem sym_open_halt_wide : ∃ R a b W, directWidth < W ∧ 178 ≤ R ∧
    PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R ∧
    (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W : Int) / 2, (R : Int) / 2] = true) ∧
    ∃ T, steps T (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = none :=
  sym_open_halt directWidth

#print axioms family_open_halt
#print axioms open_halt_families
#print axioms full_pass_open_halt
#print axioms reentryFams_shape
#print axioms reentry_open_halt
#print axioms reentryFams6_shape
#print axioms reentry6_open_halt
#print axioms full_pass_open_halt6
#print axioms no_pass_open_halt
#print axioms lane486_shape
#print axioms lane486_open_halt
#print axioms sym_open_halt
#print axioms sym_open_halt_wide

end BB6
