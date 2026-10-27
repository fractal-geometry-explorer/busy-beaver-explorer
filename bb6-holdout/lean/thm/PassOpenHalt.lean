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
* `family_open_halt`: every member of the family is a pass start with every gap at least 448 that `passTreeSym` leaves
  open at every depth (`symOpenRun` on the family, 19 rounds) and from which the machine halts (the close run on the
  family, `symCloseRun_halt`).  Both runs are evaluated by the kernel (`decide +kernel`, under a second).
* `sym_open_halt`: such pass starts at every width; `sym_open_halt_wide`: one wider than 2⁴¹ (`directWidth`).
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
#print axioms sym_open_halt
#print axioms sym_open_halt_wide

end BB6
