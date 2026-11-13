import Ends

/-!
# 1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC is the same table, mirrored and started in another state

bbchallenge 132695 is the table of this folder's machine (74982) read in a mirror, with the states renamed
(A, B, C, D, E, F of 132695 are C, F, B, A, D, E here).  So the run of 132695 from blank tape is, cell for cell in
the mirror, the run of 74982 from blank tape started in state C (`mirror_step`, `halts_mirror`).

That run reaches an arrival after 16 steps: a wall of one pair, one digit 1 and last cell 1 (`twin_arrival`).  So
132695 halts from blank tape if and only if the event system of `Ends.lean` halts from (0, [1], 1)
(`twin_halts_iff_events`, kernel only).

`twin_conversion` (compiled evaluation): the first 410,975 sweeps do not halt, and the next one is a conversion of
a wall of 410,923 pairs; `twin_halts_iff_after`: 132695 halts from blank tape if and only if the event system halts
from the counter of 410,984 digits that the conversion leaves.

The table of 132695 is restated here (`H132695.trans`, the text of its generated `Machine.lean`), because the two
folders' modules cannot be imported together.  Written by hand.
-/

namespace TM

theorem cons_head_tail (s : Tape) : cons (s 0) (tail s) = s := by
  funext n; cases n <;> rfl

section
variable {Q₁ Q₂ : Type} (δ₁ : Q₁ → Bool → Option (Bool × Dir × Q₁)) (δ₂ : Q₂ → Bool → Option (Bool × Dir × Q₂))
  (φ : Q₂ → Q₁)

/-- The other direction. -/
def Dir.flip : Dir → Dir
  | .L => .R
  | .R => .L

/-- A configuration seen in a mirror, states renamed by φ. -/
def mir (c : Cfg Q₂) : Cfg Q₁ := ⟨tail c.r, cons (c.r 0) c.l, φ c.st⟩

/-- δ₁ is δ₂ in a mirror with the states renamed. -/
def IsMirror : Prop := ∀ q b, δ₁ (φ q) b = (δ₂ q b).map (fun t => (t.1, t.2.1.flip, φ t.2.2))

variable {δ₁ δ₂ φ}

theorem mirror_step (h : IsMirror δ₁ δ₂ φ) (c : Cfg Q₂) : step δ₁ (mir φ c) = (step δ₂ c).map (mir φ) := by
  obtain ⟨l, r, q⟩ := c
  have e : step δ₁ (mir φ ⟨l, r, q⟩) = match δ₁ (φ q) (r 0) with
      | none => none
      | some (w, .R, s) => some ⟨cons w (tail r), tail (cons (r 0) l), s⟩
      | some (w, .L, s) => some ⟨tail (tail r), cons (tail r 0) (cons w (tail (cons (r 0) l))), s⟩ := rfl
  rw [e, h q (r 0)]
  unfold step
  simp only
  cases hd : δ₂ q (r 0) with
  | none => rfl
  | some t =>
    obtain ⟨w, d, s⟩ := t
    cases d
    · show some (⟨cons w (tail r), l, φ s⟩ : Cfg Q₁) = some ⟨cons w (tail r), cons (l 0) (tail l), φ s⟩
      rw [cons_head_tail]
    · rfl

theorem mirror_steps (h : IsMirror δ₁ δ₂ φ) (n : Nat) (c : Cfg Q₂) :
    steps δ₁ n (mir φ c) = (steps δ₂ n c).map (mir φ) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [steps, mirror_step h c]
    cases step δ₂ c with
    | none => rfl
    | some c' => exact ih c'

/-- A machine halts from c exactly when its mirror image halts from the mirror image of c. -/
theorem halts_mirror (h : IsMirror δ₁ δ₂ φ) (c : Cfg Q₂) : Halts δ₂ c ↔ Halts δ₁ (mir φ c) := by
  constructor
  · rintro ⟨n, c', hn, hs⟩
    exact ⟨n, mir φ c', by rw [mirror_steps h, hn]; rfl, by rw [mirror_step h, hs]; rfl⟩
  · rintro ⟨n, d, hn, hs⟩
    rw [mirror_steps h] at hn
    cases hc : steps δ₂ n c with
    | none => rw [hc] at hn; cases hn
    | some c' =>
      rw [hc] at hn
      simp only [Option.map_some, Option.some.injEq] at hn
      subst hn
      rw [mirror_step h] at hs
      refine ⟨n, c', hc, ?_⟩
      cases hs' : step δ₂ c' with
      | none => rfl
      | some x => rw [hs'] at hs; cases hs

end

end TM

namespace H132695

open TM

/-- The states of 1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC. -/
inductive St where
  | A | B | C | D | E | F
  deriving DecidableEq, Repr

/-- The transition table of 1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC, as in its own `Machine.lean`. -/
def trans : St → Bool → Option (Bool × Dir × St)
  | .A, false => some (true, .R, .B)
  | .A, true => some (true, .R, .E)
  | .B, false => some (true, .L, .C)
  | .B, true => some (true, .L, .A)
  | .C, false => some (true, .R, .A)
  | .C, true => some (false, .L, .D)
  | .D, false => some (true, .L, .C)
  | .D, true => some (false, .L, .E)
  | .E, false => some (false, .L, .F)
  | .E, true => some (false, .R, .A)
  | .F, false => none
  | .F, true => some (true, .R, .C)

/-- The machine's text form. -/
def text : String := "1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC"

/-- The state of 74982 that each state of 132695 is. -/
def toSt : St → H74982.St
  | .A => .C
  | .B => .F
  | .C => .B
  | .D => .A
  | .E => .D
  | .F => .E

theorem is_mirror : IsMirror H74982.trans trans toSt := by
  intro q b
  cases q <;> cases b <;> rfl

end H132695

namespace H74982

open TM

/-- 16 steps from blank tape in state C: the arrival with a wall of one pair, the digit 1 and last cell 1. -/
theorem twin_arrival : steps 16 (blankCfg .C) = some (arrival 1 [true] (cons true blank)) := by
  have h := blank_reaches trans (q := St.C) (n := 16)
    (c := ⟨[false, true], [true, true, true, true, true], .A⟩) (by decide +kernel)
  show TM.steps trans 16 (blankCfg St.C) = _
  rw [h]
  rfl

theorem twin_blank : mir H132695.toSt (blankCfg H132695.St.A) = blankCfg St.C := by
  show (⟨tail blank, cons (blank 0) blank, .C⟩ : Config) = ⟨blank, blank, .C⟩
  rw [show cons (blank 0) blank = blank from cons_false_blank]
  rfl

/-- **132695 is this event system too.**  1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC halts from blank tape if and
only if the event system halts from a wall of one pair, the single digit 1 and last cell 1. -/
theorem twin_halts_iff_events :
    Halts H132695.trans (blankCfg H132695.St.A) ↔ ∃ k, evrun k ⟨0, [true], true⟩ = none := by
  rw [halts_mirror H132695.is_mirror, twin_blank, ← halts_iff_events]
  exact halts_iff_of_steps twin_arrival

/-! ## The first 410,976 sweeps -/

/-- k sweeps, front first (for compiled evaluation). -/
def evrunT : Nat → Ev → Option Ev
  | 0, e => some e
  | k + 1, e =>
    match evstep e with
    | none => none
    | some e' => evrunT k e'

theorem evrun_succ_front (k : Nat) (e : Ev) : evrun (k + 1) e = (evstep e).bind (evrun k) := by
  induction k with
  | zero => simp [evrun]
  | succ k ih =>
    have h : evrun (k + 1 + 1) e = (evrun (k + 1) e).bind evstep := rfl
    rw [h, ih]
    cases evstep e with
    | none => rfl
    | some e' => rfl

theorem evrunT_eq (k : Nat) (e : Ev) : evrunT k e = evrun k e := by
  induction k generalizing e with
  | zero => rfl
  | succ k ih =>
    rw [evrun_succ_front]
    simp only [evrunT]
    cases evstep e with
    | none => rfl
    | some e' => exact ih e'

theorem halts_iff_evrun (k : Nat) (e e' : Ev) (h : evrun k e = some e') :
    Halts trans e.cfg ↔ Halts trans e'.cfg := by
  obtain ⟨s, -, hs⟩ := evrun_reach k e e' h
  exact halts_iff_of_steps hs

/-- The digits one sweep before the conversion. -/
def YT : List Bool := bits "101011011111011001101011001110000000011111111010101100011111"

/-- The counter after 410,976 sweeps. -/
def afterT : Ev := ⟨0, convDigits 410922 YT, true⟩

def sameEv (a : Option Ev) (b : Ev) : Bool :=
  match a with
  | none => false
  | some e => e.n == b.n && e.xs == b.xs && e.d == b.d

theorem sameEv_eq (a : Option Ev) (b : Ev) (h : sameEv a b = true) : a = some b := by
  cases a with
  | none => cases h
  | some e =>
    obtain ⟨n, xs, d⟩ := e
    obtain ⟨n', xs', d'⟩ := b
    simp only [sameEv, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    rfl

theorem twin_before : evrun 410975 ⟨0, [true], true⟩ = some ⟨410922, YT, true⟩ := by
  rw [← evrunT_eq]
  exact sameEv_eq _ _ (by native_decide)

/-- The first 410,975 sweeps of the event system from (0, [1], 1) do not halt; the next is a conversion of a wall
of 410,923 pairs, leaving a wall of one pair and 410,984 digits. -/
theorem twin_conversion : evrun 410976 ⟨0, [true], true⟩ = some afterT := by
  have h : evrun 410976 ⟨0, [true], true⟩ = (evrun 410975 ⟨0, [true], true⟩).bind evstep := rfl
  rw [h, twin_before]
  have hc : carry .a YT = none := by decide +kernel
  have hq : exitQ .a YT = some .b := by decide +kernel
  show evstep ⟨410922, YT, true⟩ = some afterT
  unfold evstep
  simp only [hc, hq]
  rfl

theorem afterT_length : afterT.xs.length = 410984 := by
  have h : (cind .a YT).length = 60 := by decide +kernel
  simp only [afterT, convDigits, List.length_append, List.length_replicate, List.length_cons, List.length_nil, h]

/-- 132695 halts from blank tape if and only if the event system halts from the counter after that conversion. -/
theorem twin_halts_iff_after :
    Halts H132695.trans (blankCfg H132695.St.A) ↔ ∃ k, evrun k afterT = none := by
  rw [halts_mirror H132695.is_mirror, twin_blank, ← halts_iff_events]
  exact (halts_iff_of_steps twin_arrival).trans (halts_iff_evrun _ _ _ twin_conversion)

end H74982
