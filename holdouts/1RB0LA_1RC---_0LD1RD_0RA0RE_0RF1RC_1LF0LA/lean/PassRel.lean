import PassRules

/-!
# 1RB0LA_1RC---_0LD1RD_0RA0RE_0RF1RC_1LF0LA: the pass map as a relation on lists, proved sound

A pass is: sweep right over blocks; at an empty block whose left neighbour has at least three units, *bounce*
(`n 0 1 Y` becomes `(n-2) 1 2` and the sweep goes on into `Y`); stop at one of four ends (`tail`, `zero`, `split`, `split2`,
`merge`); sweep back left over everything; arrive at the wall.  The recursion of the pass map
(`n 0 1 Y -> (n-2) 1 2 step(Y)`) is this going-on of the same rightward sweep, so no induction on the nesting is
needed: the leftward sweep `lsweep` crosses the whole list at once.

`Reach js R ks X` says: with the positive digits `js` (written `j` for the digit `j + 1`) already crossed and the
tape `R` right of the cursor `D>1 0`, the pass ends at the visit with list `ks` and rest `X`.
`reach_sound`: then the machine really goes from `L blkL(js) D>1 0 R` to the visit `111 L, ks, X`, for every `L`.
`pass_sound`: `Reach [] (ks X) ks' X'` gives a run from the visit `(L, ks, X)` to the visit `(111 L, ks', X')`.

Not covered (no constructor): an empty block whose left neighbour is `2` unless `T0` follows it (`split2`:
`ks 2 0 T0 -> ks 0 1 1 T0`), an empty block as first entry or `1 0` as first entries (the wall takes part), and a second
empty block right after an empty block.  Written by hand; kernel only.
-/

namespace H7846

open TM

/-- The pass relation (see the file header). -/
inductive Reach : List Nat → Tape → List Nat → Tape → Prop
  | tail (js : List Nat) (i : Nat) : Reach js (tailT (i + 1)) ((js ++ [i]).map (· + 1)) (tailT 0)
  | zero (js : List Nat) : Reach js (tailT 0) (js.map (· + 1) ++ [0]) (tailT 0)
  | split (js : List Nat) (m : Nat) :
      Reach (js ++ [m + 2]) (cons false (tailT 0)) ((js ++ [m, 0, 0]).map (· + 1)) (tailT 0)
  | split2 (js : List Nat) :
      Reach (js ++ [1]) (cons false (tailT 0)) (js.map (· + 1) ++ [0, 1, 1]) (tailT 0)
  | merge (js : List Nat) (i : Nat) (X : Tape) :
      Reach (js ++ [i, 0]) (cons false X) (js.map (· + 1)) (rep (i + 2) [true, true, true] X)
  | sweep (js : List Nat) (j : Nat) (R : Tape) (ks : List Nat) (X : Tape) :
      Reach (js ++ [j]) R ks X → Reach js (blkV (j + 1) R) ks X
  | bounce (js : List Nat) (m : Nat) (Y : Tape) (ks : List Nat) (X : Tape) :
      Reach (js ++ [m, 0, 1]) Y ks X → Reach (js ++ [m + 2]) (cons false (blkV 1 Y)) ks X

/-- The configuration in the middle of a rightward sweep: digits `js` crossed, `R` right of the cursor `D>1 0`. -/
def mid (L : Tape) (js : List Nat) (R : Tape) : Config :=
  ⟨sqr blkL js (cons false L), cons true (cons false R), .D⟩

/-- The bounce at an empty block followed by a block `1^3 0`, the block on the left having at least three units. -/
theorem bounce_turn (L Y : Tape) :
    steps 19 ⟨app [true, true, false, true, true, false] L, app [true, false, false, true, true, true, false] Y, .D⟩ =
      some ⟨app [true, true, false, true, true, true, false, true, true, true, false] L, cons true (cons false Y), .D⟩ := rfl

theorem fin_tail (js : List Nat) (i : Nat) (L : Tape) :
    ∃ n, steps n (mid L js (tailT (i + 1))) = some (visitX (app [true, true, true] L) ((js ++ [i]).map (· + 1)) (tailT 0)) := by
  have h2 := d_head (sqr blkL js (cons false L)) (rep (i + 2) [true, true, true] (app [true, true] blank))
  have h3 := cross_r trans (u := []) d_unit (i + 2) (app [true, true, true, false] (sqr blkL js (cons false L)))
    (app [true, true] blank)
  have h4 := tail_turn (blkL i (sqr blkL js (cons false L)))
  obtain ⟨n5, h5⟩ := lsweep (js ++ [i, 0]) (cons false L) (app [true, true, true, true] blank)
  rw [sqr_snoc2] at h5
  have e : js ++ [i, 0] = (js ++ [i]) ++ [0] := by simp
  rw [e, enc_back] at h5
  have h6 := wall_turn L (sq blkV ((js ++ [i]).map (· + 1)) (rep (0 + 1) [true, true, true] (app [true, true, true, true] blank)))
  unfold mid
  rw [enc_tail]
  exact ⟨_, steps_seq trans (steps_seq trans (steps_seq trans (steps_seq trans h2 h3) h4) h5) h6⟩

theorem fin_zero (js : List Nat) (L : Tape) :
    ∃ n, steps n (mid L js (tailT 0)) = some (visitX (app [true, true, true] L) (js.map (· + 1) ++ [0]) (tailT 0)) := by
  have h2 := turn_T0 (sqr blkL js (cons false L))
  obtain ⟨n3, h3⟩ := lsweep js (cons false L) (cons false (cons false (rep 7 [true] blank)))
  rw [enc_back0] at h3
  have h4 := wall_turn L (sq blkV (js.map (· + 1)) (cons false (rep 7 [true] blank)))
  unfold visitX
  rw [sq_snoc0]
  exact ⟨_, steps_seq trans (steps_seq trans h2 h3) h4⟩

theorem fin_split (js : List Nat) (m : Nat) (L : Tape) :
    ∃ n, steps n (mid L (js ++ [m + 2]) (cons false (tailT 0))) =
      some (visitX (app [true, true, true] L) ((js ++ [m, 0, 0]).map (· + 1)) (tailT 0)) := by
  have h2 := turn_split (blkL m (sqr blkL js (cons false L)))
  obtain ⟨n3, h3⟩ := lsweep (js ++ [m, 0, 0]) (cons false L) (cons false (rep 7 [true] blank))
  rw [enc_back0, sqr_append'] at h3
  have h4 := wall_turn L (sq blkV ((js ++ [m, 0, 0]).map (· + 1)) (rep 7 [true] blank))
  unfold mid
  rw [sqr_append']
  exact ⟨_, steps_seq trans (steps_seq trans h2 h3) h4⟩

set_option maxRecDepth 20000 in
/-- The turn at an empty block followed by `T0`, the block before it being `1^6 0`: it becomes an empty block. -/
theorem turn_split2 (L : Tape) :
    steps 91 ⟨app [true, true, false, true, true, true, false] L, app [true, false, false] (rep 7 [true] blank), .D⟩ =
      some ⟨L, app [false, false, false, false] (app [false, false, true, true, true, false, true, true, true, false]
        (rep 7 [true] blank)), .A⟩ := rfl

theorem fin_split2 (js : List Nat) (L : Tape) :
    ∃ n, steps n (mid L (js ++ [1]) (cons false (tailT 0))) =
      some (visitX (app [true, true, true] L) (js.map (· + 1) ++ [0, 1, 1]) (tailT 0)) := by
  have h2 := turn_split2 (sqr blkL js (cons false L))
  obtain ⟨n3, h3⟩ := lsweep js (cons false L)
    (cons false (app [false, true, true, true, false, true, true, true, false] (rep 7 [true] blank)))
  rw [enc_back0] at h3
  have h4 := wall_turn L (sq blkV (js.map (· + 1))
    (app [false, true, true, true, false, true, true, true, false] (rep 7 [true] blank)))
  unfold mid visitX
  rw [sqr_append', sq_append]
  exact ⟨_, steps_seq trans (steps_seq trans h2 h3) h4⟩

theorem fin_merge (js : List Nat) (i : Nat) (L X : Tape) :
    ∃ n, steps n (mid L (js ++ [i, 0]) (cons false X)) =
      some (visitX (app [true, true, true] L) (js.map (· + 1)) (rep (i + 2) [true, true, true] X)) := by
  have h2 := turn_empty (blkL i (sqr blkL js (cons false L))) X
  obtain ⟨n3, h3⟩ := lsweep (js ++ [i]) (cons false L) (app [true, true, true] X)
  rw [enc_back, sqr_append', rep_app_comm] at h3
  have h4 := wall_turn L (sq blkV (js.map (· + 1)) (rep (i + 1 + 1) [true, true, true] X))
  unfold mid
  rw [sqr_append']
  exact ⟨_, steps_seq trans (steps_seq trans h2 h3) h4⟩

theorem mid_sweep (js : List Nat) (j : Nat) (L R : Tape) :
    ∃ n, steps n (mid L js (blkV (j + 1) R)) = some (mid L (js ++ [j]) R) := by
  obtain ⟨n, h⟩ := d_block j (sqr blkL js (cons false L)) (cons true (cons false R))
  have e : cons true (cons false (blkV (j + 1) R)) = blkR j (cons true (cons false R)) := enc_visit [j] R
  unfold mid
  rw [sqr_append', e]
  exact ⟨n, h⟩

theorem mid_bounce (js : List Nat) (m : Nat) (L Y : Tape) :
    ∃ n, steps n (mid L (js ++ [m + 2]) (cons false (blkV 1 Y))) = some (mid L (js ++ [m, 0, 1]) Y) := by
  have h := bounce_turn (blkL m (sqr blkL js (cons false L))) Y
  unfold mid
  rw [sqr_append', sqr_append']
  exact ⟨19, h⟩

/-- The pass relation is sound for the machine, for every left tape `L`. -/
theorem reach_sound {js : List Nat} {R : Tape} {ks : List Nat} {X : Tape} (h : Reach js R ks X) :
    ∀ L : Tape, ∃ n, steps n (mid L js R) = some (visitX (app [true, true, true] L) ks X) := by
  induction h with
  | tail js i => exact fin_tail js i
  | zero js => exact fin_zero js
  | split js m => exact fin_split js m
  | split2 js => exact fin_split2 js
  | merge js i X => intro L; exact fin_merge js i L X
  | sweep js j R ks X _ ih =>
    intro L
    obtain ⟨n1, h1⟩ := mid_sweep js j L R
    obtain ⟨n2, h2⟩ := ih L
    exact ⟨_, steps_seq trans h1 h2⟩
  | bounce js m Y ks X _ ih =>
    intro L
    obtain ⟨n1, h1⟩ := mid_bounce js m L Y
    obtain ⟨n2, h2⟩ := ih L
    exact ⟨_, steps_seq trans h1 h2⟩

/-- From visit to visit: a derivation of the pass relation is a run of the machine, and the wall grows by 3. -/
theorem pass_sound {ks : List Nat} {X : Tape} {ks' : List Nat} {X' : Tape} (h : Reach [] (sq blkV ks X) ks' X')
    (L : Tape) : ∃ n, steps n (visitX L ks X) = some (visitX (app [true, true, true] L) ks' X') :=
  reach_sound h L

/-- An example with a bounce: `2 3 0 1 T2 -> 2 1 1 2 2 T0` (the rule `n 0 1 Y -> (n-2) 1 2 step(Y)` with `Y = T2`). -/
example (L : Tape) : ∃ n, steps n (visit L [2, 3, 0, 1] 2) = some (visit (app [true, true, true] L) [2, 1, 1, 2, 2] 0) :=
  pass_sound (ks := [2, 3, 0, 1]) (X := tailT 2) (ks' := [2, 1, 1, 2, 2]) (X' := tailT 0) (Reach.sweep [] 1 _ _ _ (Reach.sweep [1] 2 _ _ _ (Reach.bounce [1] 0 _ _ _ (Reach.tail [1, 0, 0, 1] 1)))) L

end H7846
