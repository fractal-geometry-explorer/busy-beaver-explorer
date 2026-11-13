import Blank
import EdgeCert

/-!
# A halt can only happen next to the left end

A closed tape language (`EdgeCert.lean`, found by `tools/py/bbtools/ctl.py` from windows of 6 cells, checked here by
`decide` in the kernel) covers every configuration of the run from blank tape (`reach_inv`).  Every abstract
configuration in which a halting transition (C1 or E0) can fire has the left automaton in state 34, the window
`11111#`: from that state the automaton can only read five 1s and then blank tape (`left34_prefix`).  So whenever the
machine halts, the tape to the left of the head is exactly `1 1 1 1 1` followed by blank tape (`halt_left`): every
halt happens within six cells of the left end of the tape.
-/

set_option maxRecDepth 100000

namespace H118184

open TM TM.CTL

/-- From `q` the automaton reads exactly the word `w` and then lands in a state of `B` (no accepting state on the
way). -/
def prefixOnly (M : Auto) (B : List Nat) : Nat → List Bool → Bool
  | q, [] => decide (q ∈ B)
  | q, x :: w => !(decide (q ∈ M.acc)) && M.edges.all (fun e => e.1 != q || (e.2.1 == x && prefixOnly M B e.2.2 w))

/-- The stream of the word `w` followed by blank tape. -/
def wordThenBlank : List Bool → Tape
  | [] => blank
  | x :: w => cons x (wordThenBlank w)

theorem lang_prefixOnly {M : Auto} {B : List Nat} (hB : blankOnly M B = true) :
    ∀ (w : List Bool) {q : Nat} {t : Tape}, Lang M q t → prefixOnly M B q w = true → t = wordThenBlank w
  | [], q, t, h, hp => by
    simp only [prefixOnly, decide_eq_true_eq] at hp
    exact h.blank_of_blankOnly hB hp
  | x :: w, q, t, h, hp => by
    simp only [prefixOnly, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, List.all_eq_true] at hp
    obtain ⟨hacc, hall⟩ := hp
    cases h with
    | blank hq => exact absurd hq hacc
    | @cons _ q' y t' he ht =>
      have h1 := hall _ he
      simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at h1
      obtain ⟨hy, hq'⟩ := h1
      subst hy
      rw [lang_prefixOnly hB w ht hq']
      rfl

/-- Every abstract configuration where a halting transition can fire has the left automaton in state `qh`. -/
def haltsLeftIn (MR : Auto) (S : List (St × Nat × Nat)) (qh : Nat) : Bool :=
  S.all (fun a => (MR.pops a.2.2).all (fun p => (trans a.1 p.1).isSome || a.2.1 == qh))

theorem cert_closed : TM.CTL.closed trans certL certR certS = true := by native_decide

theorem cert_starts : TM.CTL.starts certL certR certS St.A = true := by decide +kernel

theorem cert_haltsLeft : haltsLeftIn certR certS 34 = true := by native_decide

theorem left_blankOnly : blankOnly certL [39] = true := by decide +kernel

theorem left34_prefixOnly : prefixOnly certL [39] 34 [true, true, true, true, true] = true := by decide +kernel

/-- From state 34 (the window `11111#`) the left automaton accepts only five 1s followed by blank tape. -/
theorem left34_prefix {t : Tape} (h : Lang certL 34 t) : t = wordThenBlank [true, true, true, true, true] :=
  lang_prefixOnly left_blankOnly _ h left34_prefixOnly

/-- Every configuration of the run from blank tape is in the language. -/
theorem reach_inv {n : Nat} {c : Config} (h : steps n init = some c) : TM.CTL.Inv certL certR certS c :=
  TM.CTL.reach trans cert_closed cert_starts h

/-- Every halt from blank tape has exactly `1 1 1 1 1` and then blank tape to the left of the head. -/
theorem halt_left {n : Nat} {c : Config} (h : steps n init = some c) (hs : step c = none) :
    c.l = wordThenBlank [true, true, true, true, true] := by
  obtain ⟨ql, qr, hmem, hl, hr⟩ := reach_inv h
  obtain ⟨⟨x, qr'⟩, hp, hx, _⟩ := hr.pop
  have hH := cert_haltsLeft
  simp only [haltsLeftIn, List.all_eq_true] at hH
  have h1 := hH _ hmem _ hp
  simp only at hx h1
  have hnone : trans c.st x = none := by
    rw [← hx]
    rcases (step_none_iff c).1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> rfl
  rw [hnone] at h1
  simp only [Option.isSome_none, Bool.false_or, beq_iff_eq] at h1
  subst h1
  exact left34_prefix hl

end H118184
