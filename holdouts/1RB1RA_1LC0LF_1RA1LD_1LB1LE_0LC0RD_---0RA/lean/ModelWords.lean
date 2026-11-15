import Model

/-! # The transitions of the stack model, on frames and words

`py/model.py` describes the tape during a visit as a stack of frames `1^n 0^z` and, right of them, `RET(q, v)`,
`Z(v)` or `CALL(m, X)` with words over b = 110 and c = 111.  Here the frames and the two ways a word is written on
the tape are defined, and every line of the model's transition table is a theorem about the machine: the tape of the
left-hand side reaches the tape of the right-hand side in the stated number of steps.  `G` stands for the tape left
of the part that the transition touches (the remaining frames, or blank tape at the bottom of the stack), so the
theorems hold at any depth of the stack.  What stays outside Lean is only the iteration: which line applies next.

Words are lists of bits, `false` for b and `true` for c. -/

namespace H129887

open TM

/-- `n` ones, then `L` (going away from the head). -/
abbrev ones (n : Nat) (L : Tape) : Tape := rep n [true] L
/-- `n` zeros, then `L`. -/
abbrev zeros (n : Nat) (L : Tape) : Tape := rep n [false] L

/-- The stack of frames as the tape left of the active part; the top frame (nearest the head) first.  A frame
`(n, z)` is `1^n 0^z` on the tape, so reading leftwards from the head: `z` zeros, then `n` ones. -/
def frames : List (Nat × Nat) → Tape
  | [] => blank
  | (n, z) :: fs => zeros z (ones n (frames fs))

/-- A word in the phase of `CALL`: `1 1 x0, 1 1 x1, ...`, then blank tape. -/
def wX : List Bool → Tape
  | [] => blank
  | x :: w => cons true (cons true (cons x (wX w)))

/-- A nonempty word `x :: w` in the phase of `RET` and `Z` (`:: v` in the README): `x, 1 1 w0, 1 1 w1, ...`. -/
def wV (x : Bool) (w : List Bool) : Tape := cons x (wX w)

/-- `c^j w`. -/
def cpow (j : Nat) (w : List Bool) : List Bool := List.replicate j true ++ w

theorem ones_cons (n : Nat) (L : Tape) : ones n (cons true L) = cons true (ones n L) :=
  rep_app_comm n [true] L

/-- Ones next to ones are one run: a frame whose zeros are used up gives its ones to the next `CALL`. -/
theorem ones_add (a b : Nat) (L : Tape) : ones (a + b) L = ones a (ones b L) := rep_add a b [true] L

/-- Zeros next to zeros are one run: a frame pushed with no ones adds its zeros to the frame below. -/
theorem zeros_add (a b : Nat) (L : Tape) : zeros (a + b) L = zeros a (zeros b L) := rep_add a b [false] L

theorem rep3_true (j : Nat) (L : Tape) : rep j [true, true, true] L = ones (3 * j) L := by
  induction j with
  | zero => rfl
  | succ j ih => rw [rep_succ, ih, Nat.mul_succ]; rfl

theorem rep3_false (j : Nat) (L : Tape) : rep j [false, false, false] L = zeros (3 * j) L := by
  induction j with
  | zero => rfl
  | succ j ih => rw [rep_succ, ih, Nat.mul_succ]; rfl

theorem wX_cpow (j : Nat) (w : List Bool) : wX (cpow j w) = rep j [true, true, true] (wX w) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show wX (true :: cpow j w) = _
    rw [rep_succ, ← ih]; rfl

/-! ## RET -/

/-- `RET(q + 4, v) -> RET(q + 1, b v)` in 5 steps. -/
theorem ret_stride (q : Nat) (G : Tape) (x : Bool) (w : List Bool) :
    steps 5 ⟨ones (q + 3) G, cons true (wV x w), .C⟩ = some ⟨ones q G, cons true (wV false (x :: w)), .C⟩ :=
  stride1 true (ones q G) (wV x w)

/-- `RET(3, v) -> Z(b v)` in 5 steps, on a top frame with `z + 1` zeros: afterwards the head is on its last zero,
with `z` zeros on its left. -/
theorem ret3 (z : Nat) (G : Tape) (x : Bool) (w : List Bool) :
    steps 5 ⟨ones 2 (zeros (z + 1) G), cons true (wV x w), .C⟩
      = some ⟨zeros z G, cons false (wV false (x :: w)), .C⟩ :=
  stride1 false (zeros z G) (wV x w)

/-- The same at the bottom of the stack (blank tape on the left). -/
theorem ret3_bottom (x : Bool) (w : List Bool) :
    steps 5 ⟨ones 2 blank, cons true (wV x w), .C⟩ = some ⟨blank, cons false (wV false (x :: w)), .C⟩ := by
  have h := stride1 false blank (wV x w)
  rw [cons_false_blank] at h
  exact h

/-- `RET(2, v) -> Z(b v)` in 3 steps, on a top frame with `z + 2` zeros (`z` are left of the head afterwards). -/
theorem ret2 (z : Nat) (G : Tape) (x : Bool) (w : List Bool) :
    steps 3 ⟨ones 1 (zeros (z + 2) G), cons true (wV x w), .C⟩
      = some ⟨zeros z G, cons false (wV false (x :: w)), .C⟩ :=
  stride_q2 false (zeros z G) (wV x w)

/-- `RET(2, v)` on a top frame `(n + 1, 1)`: the frame is popped, `RET(n + 1, b v)`, in 3 steps. -/
theorem ret2_pop (n : Nat) (G : Tape) (x : Bool) (w : List Bool) :
    steps 3 ⟨ones 1 (zeros 1 (ones (n + 1) G)), cons true (wV x w), .C⟩
      = some ⟨ones n G, cons true (wV false (x :: w)), .C⟩ :=
  stride_q2 true (ones n G) (wV x w)

/-- `RET(2, v) -> Z(b v)` at the bottom of the stack. -/
theorem ret2_bottom (x : Bool) (w : List Bool) :
    steps 3 ⟨ones 1 blank, cons true (wV x w), .C⟩ = some ⟨blank, cons false (wV false (x :: w)), .C⟩ := by
  have h := stride_q2 false blank (wV x w)
  rw [cons_false_blank, cons_false_blank] at h
  exact h

/-- `RET(1, v) -> Z(c v)` in 3 steps, on a top frame with `z + 3` zeros (`z` are left of the head afterwards). -/
theorem ret1 (z : Nat) (G : Tape) (x : Bool) (w : List Bool) :
    steps 3 ⟨zeros (z + 3) G, cons true (wV x w), .C⟩ = some ⟨zeros z G, cons false (wV true (x :: w)), .C⟩ :=
  ret1_fill false (zeros z G) (wV x w)

/-- `RET(1, v) -> Z(c v)` at the bottom of the stack: this is how every visit of the left end begins. -/
theorem ret1_bottom (x : Bool) (w : List Bool) :
    steps 3 ⟨blank, cons true (wV x w), .C⟩ = some ⟨blank, cons false (wV true (x :: w)), .C⟩ := by
  have h := ret1_fill false blank (wV x w)
  rw [cons_false_blank, cons_false_blank, cons_false_blank] at h
  exact h

/-- `RET(1, v)` on a top frame `(n + 1, 2)`: the frame is popped, `RET(n + 1, c v)`, in 3 steps. -/
theorem ret1_pop (n : Nat) (G : Tape) (x : Bool) (w : List Bool) :
    steps 3 ⟨zeros 2 (ones (n + 1) G), cons true (wV x w), .C⟩
      = some ⟨ones n G, cons true (wV true (x :: w)), .C⟩ :=
  ret1_fill true (ones n G) (wV x w)

/-- `RET(1, v)` on a top frame `(n + 2, 1)`: it becomes the frame `(n, 1)` and `CALL(1, v)`, in 5 steps. -/
theorem ret1_one (n : Nat) (G : Tape) (x : Bool) (w : List Bool) :
    steps 5 ⟨zeros 1 (ones (n + 2) G), cons true (wV x w), .C⟩
      = some ⟨ones 1 (zeros 1 (ones n G)), wX (x :: w), .B⟩ :=
  ret1_split (ones n G) (wV x w)

/-- **The halt**: `RET(1, v)` on a top frame `(1, 1)` (one 1, one zero) with a zero below it. -/
theorem ret1_halt (G : Tape) (x : Bool) (w : List Bool) :
    ∃ c, steps 3 ⟨zeros 1 (ones 1 (cons false G)), cons true (wV x w), .C⟩ = some c ∧ step c = none :=
  halt_pattern G (wV x w)

/-! ## Z -/

/-- `Z(c^a b X) -> CALL(3a + 2, X)` in `3a + 2` steps; `G` is the tape left of the head (the rest of the top frame's
zeros; if there are none, the ones of that frame simply join the `3a + 2` ones). -/
theorem z_call (a : Nat) (G : Tape) (X : List Bool) :
    steps (3 * a + 2) ⟨G, cons false (ones (3 * a) (cons false (wX X))), .C⟩
      = some ⟨ones (3 * a + 2) G, wX X, .B⟩ := by
  have h1 := z_turn G (ones (3 * a) (cons false (wX X)))
  have h2 := a_run (3 * a) (cons true G) (wX X)
  have e : cons true (rep (3 * a) [true] (cons true G)) = ones (3 * a + 2) G := by
    show cons true (ones (3 * a) (cons true G)) = _
    rw [ones_cons]; rfl
  rw [e] at h2
  exact steps_congr trans (by omega) (steps_seq trans h1 h2)

/-- The cells of `:: c^a b X` are `3a` ones, a zero, and `X`: so `z_call` is about the word `c^a b X`. -/
theorem wV_cpow_b (a : Nat) (X : List Bool) :
    (match cpow a (false :: X) with | [] => blank | x :: w => wV x w) = ones (3 * a) (cons false (wX X)) := by
  cases a with
  | zero => rfl
  | succ a =>
    show cons true (wX (cpow a (false :: X))) = _
    rw [wX_cpow, rep3_true, Nat.mul_succ]
    show cons true (ones (3 * a) (cons true (cons true (cons false (wX X))))) = _
    rw [ones_cons, ones_cons]; rfl

/-- `Z(c^(a+1)) -> CALL(3a + 3, empty)` in `3a + 3` steps: the word ends, B arrives on blank tape. -/
theorem z_call_end (a : Nat) (G : Tape) :
    steps (3 * a + 3) ⟨G, cons false (wV true (cpow a [])), .C⟩ = some ⟨ones (3 * a + 3) G, wX [], .B⟩ := by
  have h1 := z_turn G (wV true (cpow a []))
  have e0 : wV true (cpow a []) = rep (3 * a + 1) [true] (cons false blank) := by
    show cons true (wX (cpow a [])) = _
    rw [wX_cpow, rep3_true, cons_false_blank]; rfl
  rw [e0] at h1
  have h2 := a_run (3 * a + 1) (cons true G) blank
  have e : cons true (rep (3 * a + 1) [true] (cons true G)) = ones (3 * a + 3) G := by
    show cons true (ones (3 * a + 1) (cons true G)) = _
    rw [ones_cons]; rfl
  rw [e] at h2
  rw [e0]
  exact steps_congr trans (by omega) (steps_seq trans h1 h2)

/-! ## CALL -/

/-- `CALL(m + 1, c^j b Y)`: in `9j + 7` steps the `m` ones stay as a new frame with `3j + 2` zeros, and the head
is back in `RET(1, c Y)`. -/
theorem call_word (m j : Nat) (G : Tape) (Y : List Bool) :
    steps (9 * j + 7) ⟨ones (m + 1) G, wX (cpow j (false :: Y)), .B⟩
      = some ⟨zeros (3 * j + 2) (ones m G), cons true (wV true Y), .C⟩ := by
  have h := call_cb j (ones m G) (wX Y)
  rw [rep3_false] at h
  rw [wX_cpow]
  exact h

/-- `CALL(m + 1, c^j)` at the end of the word: in `9j + 1` steps a new frame with `3j` zeros and `RET(1, c)`
(for `j = 0` there is no frame: this is `CALL(m + 1, empty) -> RET(m + 1, c)`). -/
theorem call_end (m j : Nat) (G : Tape) :
    steps (9 * j + 1) ⟨ones (m + 1) G, wX (cpow j []), .B⟩
      = some ⟨zeros (3 * j) (ones m G), cons true (wV true []), .C⟩ := by
  have h := call_c j (ones m G) blank
  rw [rep3_false, cons_false_blank] at h
  rw [wX_cpow]
  exact h

/-! ## The run from blank tape, and what a visit is -/

/-- Two steps from blank tape the machine is in `RET(1, c)` on the empty stack. -/
theorem blank_to_model : steps 2 init = some ⟨blank, cons true (wV true []), .C⟩ := rfl

/-- `RET(1, v)` on the empty stack is two steps before the head stands in B on a blank cell, with blank tape on its
left and the word `v` on its right: a visit of the left end. -/
theorem visit_of_ret1 (x : Bool) (w : List Bool) :
    steps 2 ⟨blank, cons true (wV x w), .C⟩ = some ⟨blank, cons false (wX (x :: w)), .B⟩ := rfl

end H129887
