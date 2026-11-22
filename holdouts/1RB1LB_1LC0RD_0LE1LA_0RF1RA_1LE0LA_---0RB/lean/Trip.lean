import Xor

/-!
# One round trip is a cellular automaton on cells: `c'[p] = 1 xor c[p] xor c[p+3]`

The word picture (`Xor.lean`, `Hop.lean`) needs separate rules for the walls between word strings. Here the walls
disappear. A round trip starts when the head first stands on a new leftmost cell (blank, state A). Write the cells
from there to the first `0 0` as `0 1^(k1+2) 0 1^(k2+2) 0 ... 1^(kn+2) 0 0`: runs of at least two 1s, each followed
by one 0, then a second 0. That is every tape whose stretch up to its first `00` has no isolated 1 (`0 1 0`).

* `rrun`, `rsweep`: the right sweep (B) turns each run `1^m 0` into `0^(m-1) 1 1`, in `3m - 3` steps.
* The turn: B on the second 0 writes 1 and steps left in C.
* `lstep`: the left sweep is a transducer with one step per cell. Arriving at a cell, its state names the three
  original cells to the right: E = `111`, C = `110`, B = `101`, A = `011` (`sg`). It reads what the right sweep left
  there, writes `c[p] == c[p+3]` (that is `1 xor c[p] xor c[p+3]`) and steps left.
* **`trip`**: the cells from the start cell to the first of the two 0s come back as `ca3` of themselves followed by a
  virtual `1 1 0` (`ca3 w` has cell `i` equal to `w[i] == w[i+3]`, `ca3_getD`); the second 0 becomes 1; nothing
  further right is read; the head ends one cell left of where it started, in state A, after
  `4 (Q - lo) - 6 z + 15` steps (`trip_steps`; `Q - lo` cells to the first 0 of the pair, `z` zeros up to the pair).

So on cells the machine is three interleaved copies of rule 102 (`p`, `p + 3`, `p + 6`, ... form one copy), run each
trip from the left end up to the first `00`. The words `x = 111`, `y = 110` are one copy carrying data and two copies
fixed at 1; a wall is a place where the data moves to another copy.

* `iso_birth`: if no three consecutive cells hold two 0s, an isolated 1 (`0 1 0`) in the output at `p, p+1, p+2`
  comes only from the input `0 1 1 1 1 0` at `p .. p+5`. An isolated 1 is the only thing a round trip cannot cross
  (the right sweep's token mode, where the halt lives), so this says which tapes can lead to it.
-/

namespace H696

open TM

/-! ## Runs -/

/-- The run `1^(k+2) 0`. -/
def run (k : Nat) : List Bool := List.replicate (k + 2) true ++ [false]

/-- The runs `1^(k1+2) 0 1^(k2+2) 0 ...`, left to right. -/
def runs : List Nat → List Bool
  | [] => []
  | k :: ks => run k ++ runs ks

theorem app_rep_true (n : Nat) (Z : Tape) :
    app (List.replicate n true) (cons true Z) = app (List.replicate (n + 1) true) Z := by
  induction n with
  | zero => rfl
  | succ n ih => show cons true (app (List.replicate n true) (cons true Z)) = _; rw [ih]; rfl

theorem rep_false (n : Nat) (Y : Tape) : rep n [false] Y = app (List.replicate n false) Y := by
  induction n with
  | zero => rfl
  | succ n ih => show cons false (rep n [false] Y) = cons false (app (List.replicate n false) Y); rw [ih]

/-! ## The right sweep -/

/-- B zigzags one cell along a run: `B 1 1 1 -> 0 B 1 1`. -/
theorem zz (L R : Tape) :
    steps 3 ⟨L, cons true (cons true (cons true R)), .B⟩ = some ⟨cons false L, cons true (cons true R), .B⟩ := rfl

/-- The end of a run: `B 1 1 0 -> 0 1 1 B`. -/
theorem zend (L R : Tape) :
    steps 3 ⟨L, cons true (cons true (cons false R)), .B⟩ = some ⟨cons true (cons true (cons false L)), R, .B⟩ := rfl

/-- **One run**: `B 1^(k+2) 0 -> 0^(k+1) 1 1 B`, in `3k + 3` steps. -/
theorem rrun (k : Nat) : ∀ (L R : Tape),
    steps (3 * k + 3) ⟨L, app (run k) R, .B⟩ = some ⟨cons true (cons true (rep (k + 1) [false] L)), R, .B⟩ := by
  induction k with
  | zero => intro L R; exact zend L R
  | succ k ih =>
    intro L R
    have h1 : steps 3 ⟨L, app (run (k + 1)) R, .B⟩ = some ⟨cons false L, app (run k) R, .B⟩ := zz L _
    have h2 := ih (cons false L) R
    have e : rep (k + 1) [false] (cons false L) = rep (k + 1 + 1) [false] L := rep_app_comm (k + 1) [false] L
    rw [e] at h2
    have e2 : 3 * (k + 1) + 3 = 3 + (3 * k + 3) := by omega
    rw [e2]
    exact steps_seq trans h1 h2

/-! ## The left sweep: one step per cell -/

/-- The left sweep's state names the three original cells to the right of the head. -/
def sg : Bool → Bool → Bool → St
  | true, true, true => .E
  | true, true, false => .C
  | true, false, true => .B
  | false, true, true => .A
  | _, _, _ => .F

/-- At most one 0 among three cells. -/
def vw (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

/-- **One cell of the left sweep.** Original cell `d`, original cells `a b c` to its right. The right sweep left
`!(d && a)` there; the left sweep writes `d == c` and moves on knowing `d a b`. -/
theorem lstep (d a b c : Bool) (h1 : vw a b c = true) (h2 : vw d a b = true) (X R : Tape) :
    steps 1 (onL (cons (!(d && a)) X) R (sg a b c)) = some (onL X (cons (d == c) R) (sg d a b)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp [vw] at h1 h2 <;> rfl

/-! ## One run on the way back -/

/-- What a run `1^(k+2) 0` becomes when the next three cells are `1 1 c`: cell `i` is `cell i == cell (i+3)`. -/
def blockOut : Nat → Bool → List Bool
  | 0, c => [true, true, !c]
  | j + 1, c => List.replicate j true ++ [false, true, true, !c]

/-- Is the run `1^(k+2)` longer than 2 (its third cell is 1)? -/
def lng : Nat → Bool
  | 0 => false
  | _ + 1 => true

/-- The left sweep over the image `0^(k+1) 1 1` of one run, entering with the next three cells `1 1 c` and leaving
with the run's own first three cells. -/
theorem lblock (k : Nat) (c : Bool) (X R : Tape) :
    steps (k + 3) (onL (cons true (cons true (rep (k + 1) [false] X))) R (sg true true c)) =
      some (onL X (app (blockOut k c) R) (sg true true (lng k))) := by
  -- the run's 0, then its last 1
  have h0 : steps 1 (onL (cons true (cons true (rep (k + 1) [false] X))) R (sg true true c)) =
      some (onL (cons true (rep (k + 1) [false] X)) (cons (!c) R) (sg false true true)) := by
    have := lstep false true true c (by cases c <;> rfl) rfl (cons true (rep (k + 1) [false] X)) R
    cases c <;> exact this
  have h1 : steps 1 (onL (cons true (rep (k + 1) [false] X)) (cons (!c) R) (sg false true true)) =
      some (onL (rep (k + 1) [false] X) (cons true (cons (!c) R)) (sg true false true)) :=
    lstep true false true true rfl rfl _ _
  -- the next 1
  have h2 : steps 1 (onL (cons false (rep k [false] X)) (cons true (cons (!c) R)) (sg true false true)) =
      some (onL (rep k [false] X) (cons true (cons true (cons (!c) R))) (sg true true false)) :=
    lstep true true false true rfl rfl _ _
  have h01 := steps_seq trans (steps_seq trans h0 h1) h2
  cases k with
  | zero => exact h01
  | succ j =>
    -- the cell three left of the run's 0 is the first one to see it: writes 0
    have h3 : steps 1 (onL (cons false (rep j [false] X)) (cons true (cons true (cons (!c) R))) (sg true true false)) =
        some (onL (rep j [false] X) (cons false (cons true (cons true (cons (!c) R)))) (sg true true true)) :=
      lstep true true true false rfl rfl _ _
    -- the rest of the run, all 1s with 1s three to the right
    have hr : ∀ n (Y Z : Tape), steps n (onL (rep n [false] Y) Z (sg true true true)) =
        some (onL Y (app (List.replicate n true) Z) (sg true true true)) := by
      intro n
      induction n with
      | zero => intro Y Z; rfl
      | succ n ih =>
        intro Y Z
        have a := lstep true true true true rfl rfl (rep n [false] Y) Z
        have b := ih Y (cons true Z)
        rw [app_rep_true] at b
        have hab := steps_seq trans a b
        rw [Nat.add_comm] at hab
        exact hab
    have h4 := hr j X (cons false (cons true (cons true (cons (!c) R))))
    have hall := steps_seq trans (steps_seq trans h01 h3) h4
    have e : 1 + 1 + 1 + 1 + j = j + 1 + 3 := by omega
    rw [e] at hall
    rw [show blockOut (j + 1) c = List.replicate j true ++ [false, true, true, !c] from rfl, ← app_app]
    exact hall

/-! ## All runs, there and back -/

/-- What the runs become on a round trip (the cells from the first run to the first 0 of the final `00`). -/
def out : List Nat → List Bool
  | [] => []
  | k :: ks => blockOut k (match ks with | [] => false | k' :: _ => lng k') ++ out ks

/-- The third cell of the runs (the virtual `1 1 0` after them if there are none). -/
def fl : List Nat → Bool
  | [] => false
  | k :: _ => lng k

/-- Steps of the sweep over the runs, from the right sweep to the end of the left sweep. -/
def ncost : List Nat → Nat
  | [] => 1
  | k :: ks => 3 * k + 3 + ncost ks + (k + 3)

/-- **There and back over runs**: B on the first run, a second 0 after the last run's 0. -/
theorem sweep (ks : List Nat) : ∀ (Y R : Tape),
    steps (ncost ks) ⟨Y, app (runs ks) (cons false R), .B⟩ =
      some (onL Y (app (out ks) (cons true R)) (sg true true (fl ks))) := by
  induction ks with
  | nil => intro Y R; rfl
  | cons k ks ih =>
    intro Y R
    have h1 := rrun k Y (app (runs ks) (cons false R))
    have h2 := ih (cons true (cons true (rep (k + 1) [false] Y))) R
    have h3 := lblock k (fl ks) Y (app (out ks) (cons true R))
    have e1 : app (runs (k :: ks)) (cons false R) = app (run k) (app (runs ks) (cons false R)) := by
      show app (run k ++ runs ks) _ = _; rw [← app_app]
    have e2 : app (blockOut k (fl ks)) (app (out ks) (cons true R)) = app (out (k :: ks)) (cons true R) := by
      rw [app_app]; cases ks <;> rfl
    rw [e2] at h3
    rw [e1]
    exact steps_seq trans (steps_seq trans h1 h2) h3

/-! ## The round trip -/

/-- The cellular automaton: cell `i` of `ca3 w` is `w[i] == w[i+3]` (length three less than `w`). -/
def ca3 : List Bool → List Bool
  | x :: y :: z :: w :: r => (x == w) :: ca3 (y :: z :: w :: r)
  | _ => []

theorem runs_ttf (ks : List Nat) : ∃ r, runs ks ++ [true, true, false] = true :: true :: fl ks :: r := by
  cases ks with
  | nil => exact ⟨[], rfl⟩
  | cons k ks =>
    cases k with
    | zero => exact ⟨runs ks ++ [true, true, false], rfl⟩
    | succ j =>
      exact ⟨List.replicate j true ++ [false] ++ runs ks ++ [true, true, false], by
        simp [runs, run, fl, lng, List.replicate_succ]⟩

theorem ca3_rep (j : Nat) (r : List Bool) :
    ca3 (List.replicate (j + 4) true ++ r) = true :: ca3 (List.replicate (j + 3) true ++ r) := rfl

theorem ca3_reps (j : Nat) (r : List Bool) :
    ca3 (List.replicate (j + 3) true ++ r) = List.replicate j true ++ ca3 (List.replicate 3 true ++ r) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show j + 1 + 3 = j + 4 by omega, ca3_rep, ih]; rfl

/-- **On cells, the runs come back as the cellular automaton.** -/
theorem out_ca3 (ks : List Nat) : ca3 (runs ks ++ [true, true, false]) = out ks := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    obtain ⟨r, hr⟩ := runs_ttf ks
    have hS : out (k :: ks) = blockOut k (fl ks) ++ out ks := by cases ks <;> rfl
    rw [hS, ← ih, hr]
    show ca3 ((List.replicate (k + 2) true ++ [false] ++ runs ks) ++ [true, true, false]) = _
    rw [List.append_assoc, List.append_assoc, show [false] ++ (runs ks ++ [true, true, false]) =
      false :: (runs ks ++ [true, true, false]) from rfl, hr]
    match k with
    | 0 => cases fl ks <;> rfl
    | 1 => cases fl ks <;> rfl
    | i + 2 =>
      rw [show i + 2 + 2 = (i + 1) + 3 by omega, ca3_reps]
      show List.replicate (i + 1) true ++ ca3 (true :: true :: true :: false :: true :: true :: fl ks :: r) =
        (List.replicate (i + 1) true ++ [false, true, true, !fl ks]) ++ ca3 (true :: true :: fl ks :: r)
      rw [List.append_assoc]
      cases fl ks <;> rfl

/-- **The round trip.** The head on a blank-start cell in A, then runs of at least two 1s each followed by one 0,
then a second 0. Afterwards the cells from the start cell to the first 0 of the pair are `ca3` of themselves followed
by `1 1 0`, the second 0 is 1, nothing to the right of it was read, and the head is one cell further left, in A. -/
theorem trip (ks : List Nat) (L R : Tape) :
    steps (ncost ks + 2) ⟨L, cons false (app (runs ks) (cons false R)), .A⟩ =
      some (onL L (app (ca3 (false :: runs ks ++ [true, true, false])) (cons true R)) .A) := by
  have h0 : steps 1 ⟨L, cons false (app (runs ks) (cons false R)), .A⟩ =
      some ⟨cons true L, app (runs ks) (cons false R), .B⟩ := rfl
  have h1 := sweep ks (cons true L) R
  have h2 := lstep false true true (fl ks) (by cases fl ks <;> rfl) rfl L (app (out ks) (cons true R))
  obtain ⟨r, hr⟩ := runs_ttf ks
  have e : ca3 (false :: runs ks ++ [true, true, false]) = (false == fl ks) :: out ks := by
    rw [← out_ca3 ks, List.cons_append, hr]; rfl
  rw [e]
  have h12 := steps_seq trans h0 h1
  have e2 : onL (cons true L) (app (out ks) (cons true R)) (sg true true (fl ks)) =
      onL (cons (!(false && true)) L) (app (out ks) (cons true R)) (sg true true (fl ks)) := rfl
  rw [e2] at h12
  have h := steps_seq trans h12 h2
  have e3 : 1 + ncost ks + 1 = ncost ks + 2 := by omega
  rw [e3] at h
  exact h

/-- `ca3` cell by cell. -/
theorem ca3_getD (w : List Bool) : ∀ i, i + 3 < w.length →
    (ca3 w).getD i false = (w.getD i false == w.getD (i + 3) false) := by
  induction w with
  | nil => intro i h; simp at h
  | cons x w ih =>
    intro i h
    match w, ih, h with
    | y :: z :: v :: r, ih, h =>
      cases i with
      | zero => rfl
      | succ i =>
        show (ca3 (y :: z :: v :: r)).getD i false = _
        rw [ih i (by simp at h ⊢; omega)]
        rfl

theorem ca3_length (w : List Bool) : (ca3 w).length = w.length - 3 := by
  match w with
  | x :: y :: z :: v :: r =>
    show (ca3 (y :: z :: v :: r)).length + 1 = _
    rw [ca3_length (y :: z :: v :: r)]; simp
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl

/-! ## Step count -/

/-- Cells from the start cell to the first 0 of the final pair. -/
def span : List Nat → Nat
  | [] => 0
  | k :: ks => k + 3 + span ks

theorem runs_length (ks : List Nat) : (runs ks).length = span ks := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp [runs, run, span, ih]; omega

/-- **Steps of a round trip**: with `Q - lo = span ks` (start cell to the first 0 of the pair) and `z = ks.length + 2`
zeros from the start cell to the pair, the trip takes `4 (Q - lo) - 6 z + 15` steps. -/
theorem trip_steps (ks : List Nat) : ncost ks + 2 + 6 * (ks.length + 2) = 4 * span ks + 15 := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    show 3 * k + 3 + ncost ks + (k + 3) + 2 + 6 * (ks.length + 1 + 2) = 4 * (k + 3 + span ks) + 15
    omega

/-! ## Where an isolated 1 can come from -/

/-- **Isolated 1s come from runs of four.** If every three consecutive input cells hold at most one 0, the output
cells `p, p+1, p+2` (each `c[i] == c[i+3]`) read `0 1 0` only when the input cells `p .. p+5` are `0 1 1 1 1 0`. -/
theorem iso_birth (c0 c1 c2 c3 c4 c5 : Bool)
    (h0 : vw c0 c1 c2 = true) (h1 : vw c1 c2 c3 = true) (h2 : vw c2 c3 c4 = true) (h3 : vw c3 c4 c5 = true)
    (hout : (c0 == c3) = false ∧ (c1 == c4) = true ∧ (c2 == c5) = false) :
    c0 = false ∧ c1 = true ∧ c2 = true ∧ c3 = true ∧ c4 = true ∧ c5 = false := by
  revert h0 h1 h2 h3 hout
  cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;> cases c4 <;> cases c5 <;> decide

end H696
