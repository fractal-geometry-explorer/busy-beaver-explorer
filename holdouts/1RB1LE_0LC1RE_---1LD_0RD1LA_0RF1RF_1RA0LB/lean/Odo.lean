import Machine

/-!
# 1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB: calls, hits and levels (definitions)

The vocabulary of the halting proof (`Ladder.lean`, `Halt.lean`); hand-written.

* A *call* on a left tape `T`: the head stands on a cell `1` right of `T` in a state `q`, and comes back on the cell
  right of that `1` in a state `q'`, with `T` changed into `T'`, whatever the tape to the right is (`Call`).
* A *hit* on a tape `Y` (which starts with that cell `1`): a V-hit is one call (in C, back in E), an H-hit five
  (in C, E, B, C, D, back in E, F, E, A, E).  After the hit the tape has two (H) or six (V) more cells `1` in front:
  the cells the side above hands over.
* `W p j Y`: a level `4^(j+1) s` at position `p` of the table of 16, in front of the rest `Y`.
* `Run k N Y Y' n`: `N` hits, alternately of the two kinds, the first of kind `k`, in `n` steps altogether.
-/

namespace H23376

open TM

/-- The run of `n` steps from `c` ends in a halting configuration. -/
def HaltsIn (n : Nat) (c : Config) : Prop := ∃ d, steps n c = some d ∧ step d = none

theorem HaltsIn.seq {a b : Nat} {c c' : Config} (h₁ : steps a c = some c') (h₂ : HaltsIn b c') :
    HaltsIn (a + b) c := by
  obtain ⟨d, h, hd⟩ := h₂
  exact ⟨d, steps_seq trans h₁ h, hd⟩

theorem HaltsIn.congr {a b : Nat} {c : Config} (e : a = b) (h : HaltsIn a c) : HaltsIn b c := e ▸ h

/-- A call on `T` in state `q`: back in state `q'` after `n` steps, `T` has become `T'`. -/
def Call (q q' : St) (T T' : Tape) (n : Nat) : Prop :=
  ∀ R : Tape, steps n ⟨T, cons true R, q⟩ = some ⟨cons true T', R, q'⟩

/-- A call on `T` in state `q` that does not come back: the machine halts after `n` steps. -/
def HaltCall (q : St) (T : Tape) (n : Nat) : Prop :=
  ∀ R : Tape, HaltsIn n ⟨T, cons true R, q⟩

/-- A step to the left onto the cell `1` in front of `T`, the call it starts, and the return. -/
theorem via_call {q q2 r2 : St} {x w : Bool} (hδ : trans q x = some (w, .L, q2)) {T T' : Tape} {m : Nat}
    (hc : Call q2 r2 T T' m) (Rr : Tape) :
    steps (1 + m) ⟨cons true T, cons x Rr, q⟩ = some ⟨cons true T', cons w Rr, r2⟩ := by
  have h1 : steps 1 ⟨cons true T, cons x Rr, q⟩ = some ⟨T, cons true (cons w Rr), q2⟩ := by
    simp [steps, TM.steps, TM.step, hδ]
  exact steps_seq trans h1 (hc (cons w Rr))

theorem via_halt {q q2 : St} {x w : Bool} (hδ : trans q x = some (w, .L, q2)) {T : Tape} {m : Nat}
    (hc : HaltCall q2 T m) (Rr : Tape) : HaltsIn (1 + m) ⟨cons true T, cons x Rr, q⟩ := by
  have h1 : steps 1 ⟨cons true T, cons x Rr, q⟩ = some ⟨T, cons true (cons w Rr), q2⟩ := by
    simp [steps, TM.steps, TM.step, hδ]
  exact HaltsIn.seq h1 (hc (cons w Rr))

/-- An H-hit: five calls. -/
def HitH (Y Y' : Tape) (n : Nat) : Prop :=
  ∃ (T0 T1 T2 T3 T4 T5 : Tape) (n1 n2 n3 n4 n5 : Nat), Y = cons true T0 ∧
    Call .C .E T0 T1 n1 ∧ Call .E .F T1 T2 n2 ∧ Call .B .E T2 T3 n3 ∧ Call .C .A T3 T4 n4 ∧ Call .D .E T4 T5 n5 ∧
    Y' = cons true (cons true (cons true T5)) ∧ n = n1 + n2 + n3 + n4 + n5

/-- A V-hit: one call. -/
def HitV (Y Y' : Tape) (n : Nat) : Prop :=
  ∃ (T0 T1 : Tape), Y = cons true T0 ∧ Call .C .E T0 T1 n ∧
    Y' = cons true (cons true (cons true (cons true (cons true (cons true (cons true T1))))))

/-- The first call of a hit (of either kind) halts. -/
def HC (Y : Tape) (n : Nat) : Prop := ∃ T0, Y = cons true T0 ∧ HaltCall .C T0 n

/-- The fourth call of an H-hit halts. -/
def H4 (Y : Tape) (n : Nat) : Prop :=
  ∃ (T0 T1 T2 T3 : Tape) (n1 n2 n3 n4 : Nat), Y = cons true T0 ∧
    Call .C .E T0 T1 n1 ∧ Call .E .F T1 T2 n2 ∧ Call .B .E T2 T3 n3 ∧ HaltCall .C T3 n4 ∧ n = n1 + n2 + n3 + n4

inductive Kind where
  | H | V
  deriving DecidableEq, Repr

def Kind.other : Kind → Kind
  | .H => .V
  | .V => .H

def Hit : Kind → Tape → Tape → Nat → Prop
  | .H => HitH
  | .V => HitV

/-- `N` hits, alternately H and V, the first of kind `k`. -/
def Run : Kind → Nat → Tape → Tape → Nat → Prop
  | _, 0, Y, Y', n => Y = Y' ∧ n = 0
  | k, N + 1, Y, Y', n => ∃ Y1 n1 n2, Hit k Y Y1 n1 ∧ Run k.other N Y1 Y' n2 ∧ n = n1 + n2

/-- The ten cells of a block `4`, nearest first. -/
def blockW : List Bool := [true, true, true, true, true, true, true, true, true, false]

/-- The separators of the 16 positions, as cells, nearest first. -/
def sepL : Nat → List Bool
  | 0 | 5 => [true, false, true, true, true, false, true, false, true, true, true, false]
  | 1 | 12 => [true, false, true, true, true, true, true, true, true, false, true, true, true, false]
  | 2 | 7 => [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true,
      true, true, false]
  | 3 | 14 => [true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true,
      true, true, false]
  | 4 | 9 => [true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, false]
  | 6 | 11 => [true, true, true, true, true, true, true, true, true, true, true, false, true, false, true, true, true,
      false]
  | 8 | 13 => [true, false, true, true, true, false, true, true, true, true, true, true, true, false]
  | _ => [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
      true, true, true, false]

/-- A level at position `p` with `j + 1` blocks, in front of the rest `Y`. -/
def W (p j : Nat) (Y : Tape) : Tape := rep (j + 1) blockW (app (sepL p) Y)

def kindOf (p : Nat) : Kind := if p % 2 = 0 then .H else .V

/-- The kind of hit a level passes on at position `p`, if it does. -/
def passOf : Nat → Option Kind
  | 2 | 7 | 12 => some .H
  | 4 | 10 | 15 => some .V
  | _ => none

def nxt (p : Nat) : Nat := if p = 15 then 0 else p + 1

/-- 1 at the positions where the rung gains a block. -/
def inc : Nat → Nat
  | 3 | 7 | 11 | 15 => 1
  | _ => 0

/-- Steps inside a level with `n` blocks during a hit at position `p`: `la p * n + lb p`. -/
def la (p : Nat) : Nat := if p % 2 = 0 then 112 else 56

def lb : Nat → Nat
  | 0 => 21 | 1 => 5 | 2 => 168 | 3 => 45 | 4 => 88 | 5 => 5 | 6 => 77 | 7 => 136 | 8 => 21 | 9 => 5 | 10 => 144
  | 11 => 45 | 12 => 112 | 13 => 5 | 14 => 77 | _ => 112

end H23376
