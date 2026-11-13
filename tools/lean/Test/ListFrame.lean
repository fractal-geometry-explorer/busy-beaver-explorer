import TM.ListFrame
import Test.Examples

/-! Tests of `TM.ListFrame`: a counter of any length on a toy machine, and frame maps for a halting and a looping
machine. -/

open TM

namespace Test.LF

/-- A toy machine: in A, a 1 becomes 0 and the head carries right; a 0 becomes 1 and the head turns (B), steps
back onto the digit (C); C walks left over the 0s the carry left. -/
inductive St where
  | A | B | C
  deriving DecidableEq, Repr

def trans : St → Bool → Option (Bool × Dir × St)
  | .A, true => some (false, .R, .A)
  | .A, false => some (true, .L, .B)
  | .B, x => some (x, .R, .C)
  | .C, x => some (x, .L, .C)

/-- A digit: one cell, 1 for `d ≠ 0`. -/
def D (d : Nat) (R : Tape) : Tape := cons (d != 0) R

/-- One increment, for every digit word (least significant digit under the head) and every tape on the left. -/
theorem toy_inc : ∀ (ds : List Nat) (L : Tape), DigitsLe 1 ds →
    ∃ n, steps trans n ⟨L, sq D ds blank, .A⟩ = some ⟨L, sq D (incW 1 [1] ds) blank, .C⟩ := by
  apply counter_incR trans D (cons false) blank 1 [1] .A .C
  · intro L R; exact ⟨1, rfl⟩
  · intro d hd L R
    have : d = 0 := by omega
    subst this
    refine ⟨2, ?_⟩
    show some (⟨cons (L 0) (tail L), cons true R, .C⟩ : Cfg St) = _
    rw [cons_head_tail]; rfl
  · intro L R
    refine ⟨1, ?_⟩
    show some (⟨L, cons false (cons (R 0) (tail R)), .C⟩ : Cfg St) = _
    rw [cons_head_tail]; rfl
  · intro L
    refine ⟨2, ?_⟩
    show some (⟨cons (L 0) (tail L), cons true blank, .C⟩ : Cfg St) = _
    rw [cons_head_tail]; rfl

/-- The increment adds one: 1 1 0 1 (= 11) becomes 0 0 1 1 (= 12). -/
example : incW 1 [1] [1, 1, 0, 1] = [0, 0, 1, 1] := by decide
example : valW 2 (incW 1 [1] [1, 1, 0, 1]) = valW 2 [1, 1, 0, 1] + 1 :=
  valW_incW 1 [1] rfl _ (by intro d hd; simp at hd; omega)

/-- A run of `k` ones is crossed by `carryR`. -/
example (k : Nat) (L R : Tape) :
    ∃ n, steps trans n ⟨L, pw (cons true) k R, .A⟩ = some ⟨pw (cons false) k L, R, .A⟩ :=
  carryR trans (cons true) (cons false) id .A (fun _ _ => ⟨1, rfl⟩) k L R

/-- Frame maps, halting side: BB(2)'s champion, one frame (the start), which is a stop frame. -/
example : BB2.HaltsFromBlank :=
  (frames_halts_iff BB2.trans (fun (_ : Unit) => BB2.init) (fun _ => none) (fun _ => True) (fun _ => True)
    (fun _ _ _ h => by simp at h) (fun _ _ _ h => by simp at h)
    (fun _ _ _ => Test.bb2_halts) (fun _ _ _ => trivial)
    (c0 := BB2.init) (p0 := ()) (n0 := 0) rfl trivial).mpr ⟨0, (), rfl, trivial⟩

/-- Frame maps, non-halting side: a machine that runs right on blank tape forever. -/
inductive St1 where
  | A
  deriving DecidableEq, Repr

def trans1 : St1 → Bool → Option (Bool × Dir × St1)
  | .A, _ => some (false, .R, .A)

example : ¬ Halts trans1 (blankCfg .A) := by
  apply frames_no_halt trans1 (fun (_ : Unit) => (blankCfg .A : Cfg St1)) (fun _ => some ()) (fun _ => True)
    (fun _ _ _ _ => ⟨1, Nat.one_pos, by
      show some (⟨cons false blank, tail blank, .A⟩ : Cfg St1) = _
      rw [cons_false_blank, tail_blank]; rfl⟩)
    (fun _ _ _ _ => trivial) (n0 := 0) rfl trivial
  intro k; exact ⟨(), by induction k with | zero => rfl | succ k ih => simp [iterF, ih]⟩

/-- `checkF` by `decide`. -/
example : ∀ j, j ≤ 50 → ∃ p, iterF (fun (n : Nat) => if n < 100 then some (n + 1) else none) j 0 = some p :=
  checkF_sound _ 50 0 (by decide)

/-- Run-length normal forms. -/
example : normB [(true, 2), (true, 0), (true, 1), (false, 3), (false, 0)] = [(true, 3)] := by decide
example (X : Tape) : runs [(true, 2), (false, 0), (true, 1)] X = runs [(true, 3)] X := by
  rw [← runs_normR]; rfl
example (a : Nat) (l : List (Bool × Nat)) :
    cons true (rep (a + 2) [true] (cons false (runs l blank))) = runs ((true, a + 3) :: (false, 1) :: l) blank := by
  rl_eq

end Test.LF
