import Machine

/-! # The tape moves behind the stack model

Written by `py/model_lean.py`.  `py/model.py` describes the run as a stack of frames `1^n 0^z` with, on top, one of
`RET(q, v)`: `1^(q-1) C>1 :: v`, `Z(v)`: C on the last zero of the top frame, `CALL(m, X)`: `1^m B> X`, where the
words are over b = 110 and c = 111.  Every transition of that model is one of the moves below (`Z` is `z_turn`
followed by `a_run`), and each move is proved here for any tape `L`, `R` around it.  The model itself (which move applies when,
and the bookkeeping of the frames) is checked against direct simulation, not in Lean. -/

namespace H129887

open TM

/-- A returns to the right over a run of 1s and turns the 0 behind it into a 1: `L A> 1^n 0 R` reaches
`L 1^n 1 B> R`.  (After `Z`.) -/
theorem a_run (n : Nat) (L R : Tape) :
    steps (n + 1) ⟨L, rep (n) [true] (cons false (R)), .A⟩ = some ⟨cons true (rep (n) [true] (L)), R, .B⟩ := by
  have c0 : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .A⟩ = some ⟨app [] (app [true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 1) ⟨L, rep (n) [true] (cons false (R)), .A⟩ = some ⟨rep (n) [true] (L), cons false (R), .A⟩ :=
    cross_r trans c0 (n) (L) (cons false (R))
  have h1 : steps 1 ⟨rep (n) [true] (L), cons false (R), .A⟩ = some ⟨cons true (rep (n) [true] (L)), R, .B⟩ := rfl
  exact steps_congr trans (a := (n) * 1 + (1)) (by omega) (steps_seq trans h0 (h1))

/-- B eats a run of 1s, carrying one 1 along: `L 1 B> 1^n R` reaches `L 0^n 1 B> R`. -/
theorem b_eat (n : Nat) (L R : Tape) :
    steps (3 * n) ⟨cons true (L), rep (n) [true] (R), .B⟩ = some ⟨cons true (rep (n) [false] (L)), R, .B⟩ := by
  have c0 : ∀ L R : Tape, steps 3 ⟨app [true] L, app [true] R, .B⟩ = some ⟨app [true] (app [false] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 3) ⟨cons true (L), rep (n) [true] (R), .B⟩ = some ⟨cons true (rep (n) [false] (L)), R, .B⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 3) (by omega) (h0)

/-- `n` strides in a row: `L (111)^n C>1 R` reaches `L C>1 (011)^n R`.  `RET(q + 3 n, v)` becomes `RET(q, b^n v)`. -/
theorem stride (n : Nat) (L R : Tape) :
    steps (5 * n) ⟨rep (n) [true, true, true] (L), cons true (R), .C⟩ = some ⟨L, cons true (rep (n) [false, true, true] (R)), .C⟩ := by
  have c0 : ∀ L R : Tape, steps 5 ⟨app [true, true, true] L, app [true] R, .C⟩ = some ⟨L, app [true] (app [false, true, true] R), .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 5) ⟨rep (n) [true, true, true] (L), cons true (R), .C⟩ = some ⟨L, cons true (rep (n) [false, true, true] (R)), .C⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 5) (by omega) (h0)

/-- `CALL(m, c^j b Y)`: `L 1 B> (111)^j 110 R` reaches `L 0^(3j+2) C>1 1 R`: the `1` behind the head, the block of c's and the b are now `3 j + 2` zeros (the new frame) and `RET(1, c Y)`. -/
theorem call_cb (j : Nat) (L R : Tape) :
    steps (9 * j + 7) ⟨cons true (L), rep (j) [true, true, true] (cons true (cons true (cons false (R)))), .B⟩ = some ⟨cons false (cons false (rep (j) [false, false, false] (L))), cons true (cons true (R)), .C⟩ := by
  have c0 : ∀ L R : Tape, steps 9 ⟨app [true] L, app [true, true, true] R, .B⟩ = some ⟨app [true] (app [false, false, false] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((j) * 9) ⟨cons true (L), rep (j) [true, true, true] (cons true (cons true (cons false (R)))), .B⟩ = some ⟨cons true (rep (j) [false, false, false] (L)), cons true (cons true (cons false (R))), .B⟩ :=
    cross_r trans c0 (j) (L) (cons true (cons true (cons false (R))))
  have h1 : steps 7 ⟨cons true (rep (j) [false, false, false] (L)), cons true (cons true (cons false (R))), .B⟩ = some ⟨cons false (cons false (rep (j) [false, false, false] (L))), cons true (cons true (R)), .C⟩ := rfl
  exact steps_congr trans (a := (j) * 9 + (7)) (by omega) (steps_seq trans h0 (h1))

/-- `CALL(m, c^j)` at the end of the word: `L 1 B> (111)^j 0 R` reaches `L 0^(3j) C>1 1 R`, which is `RET(1, c)` on a frame with `3 j` zeros (`j = 0`: `RET(m, c)`). -/
theorem call_c (j : Nat) (L R : Tape) :
    steps (9 * j + 1) ⟨cons true (L), rep (j) [true, true, true] (cons false (R)), .B⟩ = some ⟨rep (j) [false, false, false] (L), cons true (cons true (R)), .C⟩ := by
  have c0 : ∀ L R : Tape, steps 9 ⟨app [true] L, app [true, true, true] R, .B⟩ = some ⟨app [true] (app [false, false, false] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((j) * 9) ⟨cons true (L), rep (j) [true, true, true] (cons false (R)), .B⟩ = some ⟨cons true (rep (j) [false, false, false] (L)), cons false (R), .B⟩ :=
    cross_r trans c0 (j) (L) (cons false (R))
  have h1 : steps 1 ⟨cons true (rep (j) [false, false, false] (L)), cons false (R), .B⟩ = some ⟨rep (j) [false, false, false] (L), cons true (cons true (R)), .C⟩ := rfl
  exact steps_congr trans (a := (j) * 9 + (1)) (by omega) (steps_seq trans h0 (h1))

/-- One stride of the returning head: `L y 1 1 C>1 R` reaches `L C>y 0 1 1 R`: the head moves three cells to the
left and leaves a token `b` (in the phase `0 1 1`) behind.  `RET(q, v)` becomes `RET(q - 3, b v)`. -/
theorem stride1 (y : Bool) (L R : Tape) :
    steps 5 ⟨cons true (cons true (cons y L)), cons true R, .C⟩
      = some ⟨L, cons y (cons false (cons true (cons true R))), .C⟩ := by
  cases y <;> rfl

/-- The stride of `RET(2, v)`: the third cell is the frame's last zero: `L y 0 1 C>1 R` reaches `L C>y 0 1 1 R`. -/
theorem stride_q2 (y : Bool) (L R : Tape) :
    steps 3 ⟨cons true (cons false (cons y L)), cons true R, .C⟩
      = some ⟨L, cons y (cons false (cons true (cons true R))), .C⟩ := by
  cases y <;> rfl

/-- `RET(1, v)` on a frame with at least two zeros: `L y 0 0 C>1 R` reaches `L C>y 1 1 1 R`: two zeros are filled,
the word gets a `c` in front.  With `y = 0` this is `Z(c v)`, with `y = 1` (the frame had two zeros) the head is on
the last 1 of the frame below: `RET(n, c v)`. -/
theorem ret1_fill (y : Bool) (L R : Tape) :
    steps 3 ⟨cons false (cons false (cons y L)), cons true R, .C⟩
      = some ⟨L, cons y (cons true (cons true (cons true R))), .C⟩ := by
  cases y <;> rfl

/-- `RET(1, v)` on a frame with one zero and at least two 1s below it: `L 1 1 0 C>1 R` reaches `L 0 1 B>1 1 R`,
which is `CALL(1, v)` on a frame with one zero. -/
theorem ret1_split (L R : Tape) :
    steps 5 ⟨cons false (cons true (cons true L)), cons true R, .C⟩
      = some ⟨cons true (cons false L), cons true (cons true R), .B⟩ := rfl

/-- **The halting pattern.**  `RET(1, v)` on a frame `1 0` (one 1, one zero) above a zero: `L 0 1 0 C>1 R` halts
on its fourth step (three transitions, then F reads 0). -/
theorem halt_pattern (L R : Tape) :
    ∃ c, steps 3 ⟨cons false (cons true (cons false L)), cons true R, .C⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- `Z(v)`: C on a zero turns right: `L C>0 R` reaches `L 1 A> R`. -/
theorem z_turn (L R : Tape) : steps 1 ⟨L, cons false R, .C⟩ = some ⟨cons true L, R, .A⟩ := rfl

end H129887
