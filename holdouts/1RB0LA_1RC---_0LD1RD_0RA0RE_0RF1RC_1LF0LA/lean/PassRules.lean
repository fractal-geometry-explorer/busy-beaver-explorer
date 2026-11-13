import PassTail

/-!
# 1RB0LA_1RC---_0LD1RD_0RA0RE_0RF1RC_1LF0LA: more rules of the pass map, proved for every list

With `pass_tail` (`PassTail.lean`) these are the rules of the pass map (`py/passmap.py`) that do not recurse, each
for every list of digits before the place where the pass acts and for every left tape `L` (the wall grows by three
1s in each):

* `pass_zero`:  `ks T0 -> ks 0 T0` (no empty block in `ks`);
* `pass_split`: `ks n 0 T0 -> ks (n-2) 1 1 T0` for `n ≥ 3` (no empty block in `ks`);
* `pass_merge`: `ks a 1 0 X -> ks [1^(3a+3) X]` for `a ≥ 1` and **any** tape `X` after the empty block: the blocks
  `a` and `1` and whatever follows the empty block become one run.  With `X = T0` this is `a 1 0 T0 -> T(a+1)`,
  with `X = 1 Y` it is `a 1 0 1 Y -> (a+2) Y`.

Not proved: the recursive rule `n 0 1 Y -> (n-2) 1 2 step(Y)`, the case `n = 2` of the split, and the passes in
which the place where the pass acts is the first entry of the list (the wall takes part).
Written by hand; kernel only.
-/

namespace H7846

open TM

/-- A visit with any tape `X` after the listed blocks: `L 0 D>1 0 ks X`. -/
def visitX (L : Tape) (ks : List Nat) (X : Tape) : Config :=
  ⟨cons false L, cons true (cons false (sq blkV ks X)), .D⟩

theorem visit_eq (L : Tape) (ks : List Nat) (j : Nat) : visit L ks j = visitX L ks (tailT j) := rfl

/-- The list after the leftward sweep, when a 0 follows it. -/
theorem enc_back0 (js : List Nat) (Y : Tape) :
    sq blkB js (cons false Y) = cons false (sq blkV (js.map (· + 1)) Y) := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    show blkB j (sq blkB js (cons false Y)) = _
    rw [ih]; rfl

theorem sqr_append' {α : Type} (f : α → Tape → Tape) (ts l : List α) (X : Tape) :
    sqr f (ts ++ l) X = sqr f l (sqr f ts X) := by
  simp [sqr, List.foldl_append]

theorem sq_snoc0 (ks : List Nat) (X : Tape) : sq blkV (ks ++ [0]) X = sq blkV ks (cons false X) := by
  rw [sq_append]; rfl

set_option maxRecDepth 20000 in
/-- The turn at the end of the tail `T0`: a new empty block appears. -/
theorem turn_T0 (L : Tape) :
    steps 54 ⟨L, cons true (cons false (rep 7 [true] blank)), .D⟩ =
      some ⟨L, app [false, false, false, false] (cons false (cons false (rep 7 [true] blank))), .A⟩ := rfl

set_option maxRecDepth 20000 in
/-- The turn at an empty block followed by `T0`, the block before it having at least three units. -/
theorem turn_split (L : Tape) :
    steps 66 ⟨app [true, true, false, true, true, false] L, app [true, false, false] (rep 7 [true] blank), .D⟩ =
      some ⟨app [true, true, true, false, true, true, true, false] L,
        app [false, false, false, false] (cons false (rep 7 [true] blank)), .A⟩ := rfl

/-- The turn at an empty block after a block `1^3 0`, for any tape `X` behind the empty block. -/
theorem turn_empty (L X : Tape) :
    steps 8 ⟨app [true, true, true, false] L, app [true, false, false] X, .D⟩ =
      some ⟨L, app [false, false, false, false] (app [true, true, true] X), .A⟩ := rfl

/-- `ks T0 -> ks 0 T0`. -/
theorem pass_zero (js : List Nat) (L : Tape) :
    ∃ n, steps n (visit L (js.map (· + 1)) 0) = some (visit (app [true, true, true] L) (js.map (· + 1) ++ [0]) 0) := by
  obtain ⟨n1, h1⟩ := rsweep js (cons false L) (cons true (cons false (tailT 0)))
  rw [← enc_visit] at h1
  have h2 := turn_T0 (sqr blkL js (cons false L))
  obtain ⟨n3, h3⟩ := lsweep js (cons false L) (cons false (cons false (rep 7 [true] blank)))
  rw [enc_back0] at h3
  have h4 := wall_turn L (sq blkV (js.map (· + 1)) (cons false (rep 7 [true] blank)))
  rw [visit_eq, visit_eq]
  unfold visitX
  rw [sq_snoc0]
  exact ⟨_, steps_seq trans (steps_seq trans (steps_seq trans h1 h2) h3) h4⟩

/-- `ks n 0 T0 -> ks (n-2) 1 1 T0` for `n = m + 3`. -/
theorem pass_split (js : List Nat) (m : Nat) (L : Tape) :
    ∃ n, steps n (visit L ((js ++ [m + 2]).map (· + 1) ++ [0]) 0) =
      some (visit (app [true, true, true] L) ((js ++ [m, 0, 0]).map (· + 1)) 0) := by
  obtain ⟨n1, h1⟩ := rsweep (js ++ [m + 2]) (cons false L) (cons true (cons false (cons false (tailT 0))))
  rw [← enc_visit, sqr_append'] at h1
  have h2 := turn_split (blkL m (sqr blkL js (cons false L)))
  obtain ⟨n3, h3⟩ := lsweep (js ++ [m, 0, 0]) (cons false L) (cons false (rep 7 [true] blank))
  rw [enc_back0, sqr_append'] at h3
  have h4 := wall_turn L (sq blkV ((js ++ [m, 0, 0]).map (· + 1)) (rep 7 [true] blank))
  rw [visit_eq, visit_eq]
  unfold visitX
  rw [sq_snoc0]
  exact ⟨_, steps_seq trans (steps_seq trans (steps_seq trans h1 h2) h3) h4⟩

/-- `ks a 1 0 X -> ks [1^(3a+3) X]` for `a = i + 1` and any tape `X`. -/
theorem pass_merge (js : List Nat) (i : Nat) (L X : Tape) :
    ∃ n, steps n (visitX L ((js ++ [i, 0]).map (· + 1) ++ [0]) X) =
      some (visitX (app [true, true, true] L) (js.map (· + 1)) (rep (i + 2) [true, true, true] X)) := by
  obtain ⟨n1, h1⟩ := rsweep (js ++ [i, 0]) (cons false L) (cons true (cons false (cons false X)))
  rw [← enc_visit, sqr_append'] at h1
  have h2 := turn_empty (blkL i (sqr blkL js (cons false L))) X
  obtain ⟨n3, h3⟩ := lsweep (js ++ [i]) (cons false L) (app [true, true, true] X)
  rw [enc_back, sqr_append', rep_app_comm] at h3
  have h4 := wall_turn L (sq blkV (js.map (· + 1)) (rep (i + 1 + 1) [true, true, true] X))
  unfold visitX
  rw [sq_snoc0]
  exact ⟨_, steps_seq trans (steps_seq trans (steps_seq trans h1 h2) h3) h4⟩

end H7846
