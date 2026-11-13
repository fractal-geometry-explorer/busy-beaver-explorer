import Machine
import Gap
import Phase

/-!
# The phase at any depth, the turn and the return of 1RB0RA_1LC1RA_0LD1LD_0LE0LC_1LA0LF_---1LC

`U x y w R` is the unit `(10)^x 00 (10)^y 110 0 1^w 0 R`, and `QC b x y w L R` the configuration with the head, in
state A, on a cell `b` just left of the unit and the tape `L` to its left.  `PG = QC false`; `P x y w R` of
`Phase.lean` is `PG x y w blank R`.

* `cycle_gap`, `phase_gap`: with 6 blank cells per cycle to its left the unit runs its cycle anywhere on the tape:
  `0^(6k) A>0 U x (y+k) w` reaches `A>0 U (x+3k) y (w+2k)` in `k(8x+4y+16) + 14k²` steps.
* `cycle_ones`, `phase_ones`: against a wall of 1s the cycle takes two 1s and moves one pair:
  `1^(2k) A>1 U (x+1) (y+k) w` reaches `A>c U (x+1+k) y (w+2k)`, c the cell left of the 2k ones, in
  `k(8x+4y+24) + 6k²` steps.
* `turn`: a unit with y = 0 and 9 blank cells to its left becomes a wall of 2x+10 ones, the head on its last 1,
  followed by `1 0 1^(w+4) 0`.
* `ret`: `0^4 A>0 (10)^(x+1) 11 000` reaches `A>0 U 1 x 2`: the old x is the new y.
* `main_to_turn`, `main_from_ret`: at the left end of the tape.  A main phase `P 1 y w R` ends as a wall of 6y+12
  ones; if the trip to the right comes back as `(10)^(3y+5) 11 000`, the next main phase is `P 1 (3y+4) 2`.
-/

namespace H154944

open TM

/-- `(10)^x 00 (10)^y 110 0 1^w 0 R`. -/
def U (x y w : Nat) (R : Tape) : Tape :=
  rep x [true, false] (cons false (cons false (rep y [true, false]
    (cons true (cons true (cons false (cons false (rep w [true] (cons false R)))))))))

/-- The head in state A on a cell `b`, the unit `U x y w` right of it, `L` to the left, `R` after the unit. -/
def QC (b : Bool) (x y w : Nat) (L R : Tape) : Config := ⟨L, cons b (U x y w R), .A⟩

/-- `L A>0 U x y w R`. -/
abbrev PG (x y w : Nat) (L R : Tape) : Config := QC false x y w L R

theorem P_eq_PG (x y w : Nat) (R : Tape) : P x y w R = PG x y w blank R := rfl

theorem rot1 (b : Nat) (s : Tape) : cons true (rep b [false, true] s) = rep b [true, false] (cons true s) :=
  rep_rotate b [true] [false, true] [true, false] rfl s

/-- One cycle with six blank cells to the left. -/
theorem cycle_gap (x y w : Nat) (L R : Tape) :
    steps (8 * x + 4 * y + 30) (PG x (y + 1) w (rep 6 [false] L) R) = some (PG (x + 3) y (w + 2) L R) := by
  have h := g_cycle w x y L R
  rw [rot1] at h
  exact h

/-- The cost of k cycles from `U x (y+k) w` with blank cells to the left. -/
def gcost (x y : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (8 * x + 4 * (y + k) + 30) + gcost (x + 3) y k

theorem gcost_eq (y k : Nat) : ∀ x, gcost x y k = k * (8 * x + 4 * y + 16) + 14 * (k * k) := by
  induction k with
  | zero => intro x; simp [gcost]
  | succ k ih =>
    intro x
    rw [gcost, ih]
    simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one, Nat.mul_left_comm k]
    omega

/-- k cycles with 6k blank cells to the left. -/
theorem phase_gap' (y k : Nat) : ∀ x w L R,
    steps (gcost x y k) (PG x (y + k) w (rep (6 * k) [false] L) R) = some (PG (x + 3 * k) y (w + 2 * k) L R) := by
  induction k with
  | zero => intro x w L R; rfl
  | succ k ih =>
    intro x w L R
    have h1 := cycle_gap x (y + k) w (rep (6 * k) [false] L) R
    rw [← rep_add] at h1
    have h := steps_seq trans h1 (ih (x + 3) (w + 2) L R)
    rw [show x + 3 + 3 * k = x + 3 * (k + 1) by omega, show w + 2 + 2 * k = w + 2 * (k + 1) by omega] at h
    rw [show 6 * (k + 1) = 6 + 6 * k by omega]
    exact h

/-- k cycles with 6k blank cells to the left, in `k(8x+4y+16) + 14k²` steps (y the pairs left at the end). -/
theorem phase_gap (x y w k : Nat) (L R : Tape) :
    steps (k * (8 * x + 4 * y + 16) + 14 * (k * k)) (PG x (y + k) w (rep (6 * k) [false] L) R) =
      some (PG (x + 3 * k) y (w + 2 * k) L R) := by
  rw [← gcost_eq]; exact phase_gap' y k x w L R

/-- One cycle against a wall of 1s: the head on the last 1 of the wall, `c` the cell after the next 1. -/
theorem cycle_ones (c : Bool) (x y w : Nat) (L R : Tape) :
    steps (8 * x + 4 * y + 30) (QC true (x + 1) (y + 1) w (cons true (cons c L)) R) =
      some (QC c (x + 2) y (w + 2) L R) := by
  have h := g_q w x y (cons c L) R
  rw [rot1] at h
  have h2 : ∀ s : Tape, steps 1 ⟨cons c L, cons false s, .E⟩ = some ⟨L, cons c (cons true s), .A⟩ := fun _ => rfl
  exact steps_congr trans (by omega) (steps_seq trans h (h2 _))

/-- The cost of k cycles from `U (x+1) (y+k) w` against a wall of 1s. -/
def qcost (x y : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (8 * x + 4 * (y + k) + 30) + qcost (x + 1) y k

theorem qcost_eq (y k : Nat) : ∀ x, qcost x y k = k * (8 * x + 4 * y + 24) + 6 * (k * k) := by
  induction k with
  | zero => intro x; simp [qcost]
  | succ k ih =>
    intro x
    rw [qcost, ih]
    simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one, Nat.mul_left_comm k]
    omega

/-- k+1 cycles against a wall of 2k+2 ones (the head on the last of them); `c` is the cell left of the wall. -/
theorem phase_ones' (c : Bool) (y k : Nat) : ∀ x w L R,
    steps (qcost x y (k + 1)) (QC true (x + 1) (y + (k + 1)) w (rep k [true, true] (cons true (cons c L))) R) =
      some (QC c (x + 1 + (k + 1)) y (w + 2 * (k + 1)) L R) := by
  induction k with
  | zero => intro x w L R; exact cycle_ones c x y w L R
  | succ k ih =>
    intro x w L R
    have h1 := cycle_ones true x (y + (k + 1)) w (rep k [true, true] (cons true (cons c L))) R
    have h := steps_seq trans h1 (ih (x + 1) (w + 2) L R)
    rw [show x + 1 + 1 + (k + 1) = x + 1 + (k + 1 + 1) by omega,
      show w + 2 + 2 * (k + 1) = w + 2 * (k + 1 + 1) by omega] at h
    exact h

/-- k+1 cycles against a wall of 1s, in `(k+1)(8x+4y+24) + 6(k+1)²` steps. -/
theorem phase_ones (c : Bool) (x y w k : Nat) (L R : Tape) :
    steps ((k + 1) * (8 * x + 4 * y + 24) + 6 * ((k + 1) * (k + 1)))
        (QC true (x + 1) (y + (k + 1)) w (rep k [true, true] (cons true (cons c L))) R) =
      some (QC c (x + 1 + (k + 1)) y (w + 2 * (k + 1)) L R) := by
  rw [← qcost_eq]; exact phase_ones' c y k x w L R

theorem ones2 (x : Nat) (s : Tape) : rep x [true, true] s = rep (2 * x) [true] s := by
  induction x with
  | zero => rfl
  | succ x ih => rw [show 2 * (x + 1) = 2 * x + 1 + 1 by omega, rep_succ, rep_succ, rep_succ, ih]; rfl

/-- The turn: a unit with y = 0 and nine blank cells to its left becomes a wall of 2x+10 ones with the head on
the last of them, followed by `1 0 1^(w+4) 0 R`. -/
theorem turn (x w : Nat) (L R : Tape) :
    steps (14 * x + 60) (PG x 0 w (rep 9 [false] L) R) =
      some ⟨rep (2 * x + 9) [true] L, cons true (cons true (cons false (rep (w + 4) [true] (cons false R)))), .A⟩ := by
  have h := g_turn w x L R
  rw [ones2] at h
  rw [rep_add]
  exact h

/-- The return: `0^4 A>0 (10)^(x+1) 11 000 R` reaches `A>0 U 1 x 2 R`. -/
theorem ret (x : Nat) (L R : Tape) :
    steps (4 * x + 16) ⟨rep 4 [false] L, cons false (rep (x + 1) [true, false]
        (cons true (cons true (cons false (cons false (cons false R)))))), .A⟩ = some (PG 1 x 2 L R) := by
  have h := g_ret x L R
  rw [rot1] at h
  exact h

theorem blank_rep (n : Nat) : rep n [false] blank = blank := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep_succ, ih]; exact cons_false_blank

/-- A main phase to its turn: `P 1 y w R` reaches a wall of 6y+12 ones, the head on the last of them, followed by
`1 0 1^(w+2y+4) 0 R`. -/
theorem main_to_turn (y w : Nat) (R : Tape) :
    steps (pcost 1 y + (14 * (1 + 3 * y) + 60)) (P 1 y w R) =
      some ⟨rep (6 * y + 11) [true] blank,
        cons true (cons true (cons false (rep (w + 2 * y + 4) [true] (cons false R)))), .A⟩ := by
  have h1 := phase y 1 w R
  have h2 := turn (1 + 3 * y) (w + 2 * y) blank R
  rw [blank_rep] at h2
  have h := steps_seq trans h1 h2
  rw [show 2 * (1 + 3 * y) + 9 = 6 * y + 11 by omega] at h
  exact h

/-- Back at the left end: `A>0 (10)^(x+1) 11 000 R` reaches the main phase `P 1 x 2 R`. -/
theorem main_from_ret (x : Nat) (R : Tape) :
    steps (4 * x + 16) ⟨blank, cons false (rep (x + 1) [true, false]
        (cons true (cons true (cons false (cons false (cons false R)))))), .A⟩ = some (P 1 x 2 R) := by
  have h := ret x blank R
  rw [blank_rep] at h
  exact h

end H154944
