import Rules

/-!
# 1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LA---: the ordinary pass, for every list of blocks

Write `S = 1 1 1 0 1` (a separator), `blk n = (10)^(n+3) S`, and for a list `ms = [m1, ..., mk]`
`blocks ms = blk m1 ... blk mk`.  The frontier is `front p q = (10)^(p+3) 1 (10)^(q+3) 1 1 1 0`.
An arrival at the left end in state A is

  `Arr c ms p q R = 0^inf A> 1 0 0 blk c (blocks ms) front p q R`.

`pass`: for every counter c, every list ms, every p, q and every tape R,
`Arr (c+1) ms p (q+1) R` reaches `Arr c ms (p+4) q R`.  The counter loses one copy of `10`, and the first
frontier block gains four while the second loses one, and every block in between comes back unchanged.

The proof chains the rules `pass_*` of `Rules.lean` by induction over the list: rightward (`pass_right`, each
separator re-encoded as `1 1 0 1 0`), the turn (`pass_front`), leftward (`pass_sep`, `pass_left`), and the left end
(`pass_end`); `zz_eq` shows the re-encoded tape is the original block list again.  Written by hand.
-/

namespace H8754

open TM

/-- `1 1 1 0 1 R`. -/
def S (R : Tape) : Tape := cons true (cons true (cons true (cons false (cons true R))))
/-- `(10)^(n+3) 1 1 1 0 1 R`. -/
def blk (n : Nat) (R : Tape) : Tape := rep (n + 3) [true, false] (S R)
/-- The blocks of a list, left to right. -/
def blocks : List Nat → Tape → Tape
  | [], R => R
  | m :: ms, R => blk m (blocks ms R)
/-- The frontier `(10)^(p+3) 1 (10)^(q+3) 1 1 1 0 R`. -/
def front (p q : Nat) (R : Tape) : Tape :=
  rep (p + 3) [true, false] (cons true (rep (q + 3) [true, false]
    (cons true (cons true (cons true (cons false R))))))
/-- An arrival at the left end. -/
def Arr (c : Nat) (ms : List Nat) (p q : Nat) (R : Tape) : Config :=
  ⟨blank, cons true (cons false (cons false (blk c (blocks ms (front p q R))))), .A⟩

/-- Left of the head after the rightward pass crossed a block: `L (10)^(n+3) 1 1 0 1 0`. -/
def LB (n : Nat) (L : Tape) : Tape :=
  cons false (cons true (cons false (cons true (cons true (rep (n + 3) [false, true] L)))))
/-- Left of the head after crossing the blocks of ms (the last one nearest). -/
def lfold : List Nat → Tape → Tape
  | [], L => L
  | m :: ms, L => lfold ms (LB m L)
/-- `1 0 1 0 1 0 1 R`. -/
def P7 (R : Tape) : Tape :=
  cons true (cons false (cons true (cons false (cons true (cons false (cons true R))))))
/-- A block as the leftward pass leaves it: `(01)^m 1 1 0 1 1 0 1 0 1 0 1 Y`. -/
def Z (m : Nat) (Y : Tape) : Tape :=
  rep m [false, true] (cons true (cons true (cons false (cons true (P7 Y)))))
def zz : List Nat → Tape → Tape
  | [], Y => Y
  | m :: ms, Y => Z m (zz ms Y)

theorem rsweep (ms : List Nat) (L R : Tape) :
    ∃ s, steps s ⟨L, cons false (blocks ms R), .A⟩ = some ⟨lfold ms L, cons false R, .A⟩ := by
  induction ms generalizing L with
  | nil => exact ⟨0, rfl⟩
  | cons m ms ih =>
    obtain ⟨s, h⟩ := ih (LB m L)
    exact ⟨_, steps_seq trans (pass_right (m + 3) L (blocks ms R)) h⟩

theorem lsweep (ms : List Nat) (L Y : Tape) :
    ∃ s, steps s ⟨lfold ms L, cons true (cons false Y), .A⟩ = some ⟨L, cons true (cons false (zz ms Y)), .A⟩ := by
  induction ms generalizing L with
  | nil => exact ⟨0, rfl⟩
  | cons m ms ih =>
    obtain ⟨s, h⟩ := ih (LB m L)
    have h1 := pass_sep (rep (m + 3) [false, true] L) (zz ms Y)
    have h2 := pass_left m L (zz ms Y)
    exact ⟨_, steps_seq trans h (steps_seq trans h1 h2)⟩

theorem rot1 (n : Nat) (W : Tape) : cons true (rep n [false, true] W) = rep n [true, false] (cons true W) :=
  rep_rotate n [true] [false, true] [true, false] rfl W

/-- `1 0 1 0 1 Z m Y = (10)^(m+2) S (P7 Y)`. -/
theorem z5 (m : Nat) (Y : Tape) :
    cons true (cons false (cons true (cons false (cons true (Z m Y))))) = rep (m + 2) [true, false] (S (P7 Y)) := by
  simp only [Z, rot1, rep_succ, app_cons, app_nil, S]

theorem z7 (m : Nat) (Y : Tape) : P7 (Z m Y) = blk m (P7 Y) := by
  have h := z5 m Y
  simp only [P7, blk] at h ⊢
  rw [h]; rfl

theorem zz_eq (ms : List Nat) (Y : Tape) : P7 (zz ms Y) = blocks ms (P7 Y) := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simp only [zz, blocks, z7, ih]

theorem front_eq (p q : Nat) (R : Tape) :
    P7 (rep (p + 3) [false, true] (cons false (cons true (rep (q + 3) [true, false]
      (cons true (cons true (cons true (cons false R)))))))) = front (p + 4) q R := by
  simp only [P7, front, rot1]
  rw [show p + 4 + 3 = 3 + ((p + 3) + 1) by omega, rep_add 3 (p + 3 + 1), rep_add (p + 3) 1]
  simp only [rep_succ, rep_zero, app_cons, app_nil]

/-- The ordinary pass, for every counter, every list of blocks and every frontier. -/
theorem pass (c : Nat) (ms : List Nat) (p q : Nat) (R : Tape) :
    ∃ s, steps s (Arr (c + 1) ms p (q + 1) R) = some (Arr c ms (p + 4) q R) := by
  have h0 := pass_start (blk (c + 1) (blocks ms (front p (q + 1) R)))
  have e1 : blk (c + 1) (blocks ms (front p (q + 1) R)) = blocks ((c + 1) :: ms) (front p (q + 1) R) := rfl
  rw [e1] at h0
  obtain ⟨s1, h1⟩ := rsweep ((c + 1) :: ms) (cons false (cons true (cons false (cons true (cons false (cons true blank))))))
    (front p (q + 1) R)
  have h2 := pass_front p (q + 1) (lfold ((c + 1) :: ms)
    (cons false (cons true (cons false (cons true (cons false (cons true blank))))))) R
  obtain ⟨s3, h3⟩ := lsweep ((c + 1) :: ms) (cons false (cons true (cons false (cons true (cons false (cons true blank))))))
    (rep (p + 3) [false, true] (cons false (cons true (rep (q + 1 + 2) [true, false]
      (cons true (cons true (cons true (cons false R))))))))
  have h4 := pass_end (zz ((c + 1) :: ms) (rep (p + 3) [false, true] (cons false (cons true (rep (q + 1 + 2) [true, false]
      (cons true (cons true (cons true (cons false R)))))))))
  have h := steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 h4)))
  refine ⟨_, h.trans ?_⟩
  have e2 := z5 (c + 1) (zz ms (rep (p + 3) [false, true] (cons false (cons true (rep (q + 1 + 2) [true, false]
      (cons true (cons true (cons true (cons false R)))))))))
  simp only [zz, Arr]
  rw [e2, zz_eq, show q + 1 + 2 = q + 3 by omega, front_eq]
  rfl

end H8754
