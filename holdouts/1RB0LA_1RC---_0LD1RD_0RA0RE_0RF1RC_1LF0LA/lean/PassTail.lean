import Sweeps

/-!
# 1RB0LA_1RC---_0LD1RD_0RA0RE_0RF1RC_1LF0LA: one rule of the pass map, proved for every list

A *visit* is the configuration `L 0 D>1 0 k1 k2 ... kn Tj`: the head in state D on a single 1 between two 0s, left
of it any tape `L` (in the run: the wall), right of it the blocks `1^(3k) 0` for the digits `k` of the list and the
tail `Tj = 1^(7+3j)` followed by blank tape (`visit L ks j`).

`pass_tail`: if no digit of the list is 0 and the tail is `Tj` with `j ≥ 1`, the machine goes from the visit with
list `ks`, tail `Tj` to the visit with list `ks ++ [j]`, tail `T0`, and three more 1s on the left (the wall grows
by 3).  This is the rule `... Tj -> ... j T0` of the pass map (`py/passmap.py`), for every list and every `L`.

The proof chains the rightward sweep (`rsweep`), the turn at the end of the tail (`tail_turn`, 32 steps), the
leftward sweep (`lsweep`) and the arrival at the wall (`wall_turn`, 15 steps).  Written by hand; kernel only.
-/

namespace H7846

open TM

/-- The tail `Tj`: `1^(7+3j)`, then blank tape. -/
def tailT (j : Nat) : Tape := rep (7 + 3 * j) [true] blank

/-- The block of a digit `k` at a visit: `1^(3k) 0`. -/
def blkV (k : Nat) (X : Tape) : Tape := rep k [true, true, true] (cons false X)

/-- The visit `L 0 D>1 0 ks Tj`. -/
def visit (L : Tape) (ks : List Nat) (j : Nat) : Config :=
  ⟨cons false L, cons true (cons false (sq blkV ks (tailT j))), .D⟩

theorem rep3_shift (j : Nat) : ∀ Z : Tape, rep (j + 1) [true, true, true] Z =
    cons true (cons true (rep j [true, true, true] (cons true Z))) := by
  induction j with
  | zero => intro Z; rfl
  | succ j ih =>
    intro Z
    show cons true (cons true (cons true (rep (j + 1) [true, true, true] Z))) = _
    rw [ih Z]; rfl

/-- The list at a visit, as the rightward sweep reads it. -/
theorem enc_visit (js : List Nat) (X : Tape) :
    cons true (cons false (sq blkV (js.map (· + 1)) X)) = sq blkR js (cons true (cons false X)) := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    show cons true (cons false (rep (j + 1) [true, true, true] (cons false (sq blkV (js.map (· + 1)) X)))) =
      blkR j (sq blkR js (cons true (cons false X)))
    rw [← ih, rep3_shift]; rfl

/-- The list after the leftward sweep, as a list of visit blocks behind one 0. -/
theorem enc_back (js : List Nat) (m : Nat) (Y : Tape) :
    sq blkB (js ++ [m]) Y = cons false (sq blkV (js.map (· + 1)) (rep (m + 1) [true, true, true] Y)) := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    show blkB j (sq blkB (js ++ [m]) Y) = _
    rw [ih]; rfl

/-- The tail `T(i+1)` behind `1 0`, as the rightward sweep reads it: a block and `1 1`. -/
theorem enc_tail (i : Nat) :
    cons true (cons false (tailT (i + 1))) = blkR (i + 2) (app [true, true] blank) := by
  have h : ∀ i : Nat, rep (10 + 3 * i) [true] blank =
      cons true (cons true (rep (i + 2) [true, true, true] (app [true, true] blank))) := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      have e : 10 + 3 * (i + 1) = (10 + 3 * i) + 3 := by omega
      rw [e]
      show cons true (cons true (cons true (rep (10 + 3 * i) [true] blank))) = _
      rw [ih]; rfl
  have e : 7 + 3 * (i + 1) = 10 + 3 * i := by omega
  show cons true (cons false (rep (7 + 3 * (i + 1)) [true] blank)) = _
  rw [e, h i]; rfl

/-- The turn at the end of the tail: D at `1 1` and blank tape, two `011` on its left. -/
theorem tail_turn (L : Tape) :
    steps 32 ⟨app [true, true, false, true, true, false] L, app [true, true] blank, .D⟩ =
      some ⟨app [true, true, true, false] L, app [false, false, false, false] (app [true, true, true, true] blank), .A⟩ := rfl

/-- The arrival at the wall: A at `0 000 0` with a 0 on its left; three 1s are added on the left. -/
theorem wall_turn (L X : Tape) :
    steps 15 ⟨cons false L, app [false, false, false, false] (cons false X), .A⟩ =
      some ⟨cons false (app [true, true, true] L), cons true (cons false X), .D⟩ := rfl

theorem sqr_snoc2 {α : Type} (f : α → Tape → Tape) (ts : List α) (a b : α) (X : Tape) :
    sqr f (ts ++ [a, b]) X = f b (f a (sqr f ts X)) := by
  simp [sqr, List.foldl_append]

/-- The pass rule `... Tj -> ... j T0` (no empty block in the list, `j = i + 1`), for every list and every left tape. -/
theorem pass_tail (js : List Nat) (i : Nat) (L : Tape) :
    ∃ n, steps n (visit L (js.map (· + 1)) (i + 1)) =
      some (visit (app [true, true, true] L) ((js ++ [i]).map (· + 1)) 0) := by
  obtain ⟨n1, h1⟩ := rsweep js (cons false L) (cons true (cons false (tailT (i + 1))))
  rw [← enc_visit] at h1
  rw [enc_tail] at h1
  have h2 := d_head (sqr blkL js (cons false L)) (rep (i + 2) [true, true, true] (app [true, true] blank))
  have h3 := cross_r trans (u := []) d_unit (i + 2) (app [true, true, true, false] (sqr blkL js (cons false L)))
    (app [true, true] blank)
  have h4 := tail_turn (blkL i (sqr blkL js (cons false L)))
  obtain ⟨n5, h5⟩ := lsweep (js ++ [i, 0]) (cons false L) (app [true, true, true, true] blank)
  rw [sqr_snoc2] at h5
  have e : js ++ [i, 0] = (js ++ [i]) ++ [0] := by simp
  rw [e, enc_back] at h5
  have h6 := wall_turn L (sq blkV ((js ++ [i]).map (· + 1)) (rep (0 + 1) [true, true, true] (app [true, true, true, true] blank)))
  exact ⟨_, steps_seq trans (steps_seq trans (steps_seq trans (steps_seq trans (steps_seq trans h1 h2) h3) h4) h5) h6⟩

end H7846
