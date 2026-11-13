import CTL4
import Blank

/-!
# Every halt is at the left edge

The closed tape language of `CTL4.lean` (windows of 4 cells) allows a halt in one abstract configuration only, and
there the left automaton is in a state that accepts the blank stream alone.  So whenever the machine halts from
blank tape, every cell to the left of the head is 0: the head is past the left end of everything written.

`halt_left_blank` is the left-hand mirror of `TM.CTL.halt_tail_blank` (which is about the right side), proved here
for this machine's certificate.
-/

namespace H71477

open TM TM.CTL

/-- Every abstract configuration where a halting transition can fire has a left state in `BL`. -/
def haltsBlankL (MR : Auto) (S : List (St × Nat × Nat)) (BL : List Nat) : Bool :=
  S.all (fun a => (MR.pops a.2.2).all (fun p => (trans a.1 p.1).isSome || decide (a.2.1 ∈ BL)))

/-- The left automaton's states that accept only the blank stream. -/
def certBL : List Nat := [11]

theorem halt_left_of {ML MR : Auto} {S : List (St × Nat × Nat)} {BL : List Nat} (hB : blankOnly ML BL = true)
    (hH : haltsBlankL MR S BL = true) {c : Cfg St} (hc : Inv ML MR S c) (hs : TM.step trans c = none) :
    c.l = TM.blank := by
  obtain ⟨ql, qr, hmem, hl, hr⟩ := hc
  obtain ⟨⟨x, qr'⟩, hp, hx, _⟩ := hr.pop
  simp only [haltsBlankL, List.all_eq_true] at hH
  have h1 := hH _ hmem _ hp
  simp only at hx h1
  unfold TM.step at hs
  rw [hx] at hs
  cases hδ : trans c.st x with
  | none =>
    rw [hδ] at h1
    simp only [Option.isSome_none, Bool.false_or, decide_eq_true_eq] at h1
    exact hl.blank_of_blankOnly hB h1
  | some t =>
    rw [hδ] at hs
    obtain ⟨w, d, s'⟩ := t
    cases d <;> cases hs

theorem cert_closed : closed trans certL certR certS = true := by decide +kernel

theorem cert_starts : starts certL certR certS St.A = true := by decide +kernel

theorem cert_blankOnlyL : blankOnly certL certBL = true := by decide +kernel

theorem cert_haltsBlankL : haltsBlankL certR certS certBL = true := by decide +kernel

/-- Any configuration of the run from blank tape at which the machine halts is in state E, reading a 0, with blank
tape left of the head. -/
theorem halt_left_blank {n : Nat} {c : Config} (h : steps n init = some c) (hs : step c = none) :
    c.st = .E ∧ c.r 0 = false ∧ c.l = TM.blank :=
  ⟨((step_none_iff c).1 hs).1, ((step_none_iff c).1 hs).2,
    halt_left_of cert_blankOnlyL cert_haltsBlankL (reach trans cert_closed cert_starts h) hs⟩

end H71477
