import Rules

/-!
# 1RB1LF_1RC0RA_0RD1RA_1RE1LA_0LA---_1RF0LD: the decrement for every number of borrows

`Rules.lean` proves one visit of the left end for one, two and three bits (`dec_1` .. `dec_3`).  This file proves it
for every bit list.  The tape right of the head, at the left end in state A, reads

  `0 (10)^X b_1 (10)^Y_1 b_2 (10)^Y_2 ... b_k (10)^Y_k R`

(`event X bl R`, with `bl` the list of pairs `(b_i, Y_i)`).  When the lowest set bit is `b_j` and the blocks
`Y_1 .. Y_j` are not empty (`reg bl`), one visit sets `b_1 .. b_(j-1)` to 1 and `b_j` to 0, takes one copy from
`Y_j`, adds two to `X` and moves the left end two cells left, in `6 (X + Y_1 + ... + Y_(j-1)) + 10` steps
(`dec_step`).  The visit is built from ten short passes, each checked by `rfl`, and the three crossings of
`Rules.lean`.
-/

namespace H180268

open TM

/-! ## The short passes -/

theorem u_start (L R : Tape) : steps 1 ⟨L, cons false R, .A⟩ = some ⟨cons true L, R, .B⟩ := rfl

theorem u_zero (L R : Tape) :
    steps 3 ⟨L, cons false (cons true (cons false R)), .B⟩ = some ⟨cons true (cons true (cons true L)), R, .B⟩ := rfl

theorem u_turn (L R : Tape) :
    steps 2 ⟨L, cons true (cons true (cons false R)), .B⟩ = some ⟨L, cons false (cons true (cons false R)), .F⟩ := rfl

theorem u_f111 (L R : Tape) :
    steps 5 ⟨cons true (cons true (cons true L)), cons false (cons true R), .F⟩ =
      some ⟨L, cons true (cons false (cons true (cons true (cons false R)))), .D⟩ := rfl

theorem u_d111 (L R : Tape) :
    steps 3 ⟨cons true (cons true (cons true L)), cons true R, .D⟩ =
      some ⟨L, cons true (cons false (cons true (cons true R))), .D⟩ := rfl

theorem u_endD (R : Tape) :
    steps 5 ⟨cons true blank, cons true R, .D⟩ = some ⟨blank, cons false (cons true (cons false (cons true R))), .A⟩ := rfl

theorem u_endF (R : Tape) :
    steps 7 ⟨cons true blank, cons false (cons true R), .F⟩ =
      some ⟨blank, cons false (cons true (cons false (cons true (cons false R)))), .A⟩ := rfl

/-! ## The way out: zero bits -/

/-- Zero bits with blocks `y + 1` each. -/
def encZ : List Nat → Tape → Tape
  | [], R => R
  | y :: ys, R => cons false (rep (y + 1) [true, false] (encZ ys R))

/-- What the way out leaves on the left: each zero bit becomes `111`, its block `(10)^y` behind it. -/
def outL : List Nat → Tape → Tape
  | [], L => L
  | y :: ys, L => outL ys (rep y [true, false] (cons true (cons true (cons true L))))

def sumO : List Nat → Nat
  | [] => 0
  | y :: ys => 2 * y + 3 + sumO ys

theorem out_run (ys : List Nat) : ∀ (L R : Tape),
    steps (sumO ys) ⟨L, encZ ys R, .B⟩ = some ⟨outL ys L, R, .B⟩ := by
  induction ys with
  | nil => intro L R; rfl
  | cons y ys ih =>
    intro L R
    have h1 := u_zero L (rep y [true, false] (encZ ys R))
    have h2 := cross_B_r_10 y (cons true (cons true (cons true L))) (encZ ys R)
    have h3 := ih (rep y [true, false] (cons true (cons true (cons true L)))) R
    exact steps_congr trans (by simp [sumO]; omega) (steps_seq trans h1 (steps_seq trans h2 h3))

theorem outL_snoc (ys : List Nat) (y : Nat) : ∀ L : Tape,
    outL (ys ++ [y]) L = rep y [true, false] (cons true (cons true (cons true (outL ys L)))) := by
  induction ys with
  | nil => intro L; rfl
  | cons a ys ih => intro L; exact ih _

/-! ## The way back -/

/-- What the way back leaves on the right: each `111` becomes `011`, its block `(01)^y` behind it. -/
def retR : List Nat → Tape → Tape
  | [], S => S
  | y :: ys, S => cons false (cons true (cons true (rep y [false, true] (retR ys S))))

def sumR : List Nat → Nat
  | [] => 0
  | y :: ys => 4 * y + 3 + sumR ys

theorem ret_run (ys : List Nat) : ∀ (L S : Tape),
    steps (sumR ys) ⟨outL ys L, cons true S, .D⟩ = some ⟨L, cons true (retR ys S), .D⟩ := by
  induction ys with
  | nil => intro L S; rfl
  | cons y ys ih =>
    intro L S
    have h1 := ih (rep y [true, false] (cons true (cons true (cons true L)))) S
    have h2 := cross_D_l_01 y (cons true (cons true (cons true L))) (retR ys S)
    have h3 := u_d111 L (rep y [false, true] (retR ys S))
    exact steps_congr trans (by simp [sumR]; omega) (steps_seq trans h1 (steps_seq trans h2 h3))

/-! ## Reading the result -/

/-- One bits with blocks `y + 1` each. -/
def encO : List Nat → Tape → Tape
  | [], R => R
  | y :: ys, R => cons true (rep (y + 1) [true, false] (encO ys R))

/-- `1 (01)^n 0 = (10)^(n+1)`. -/
theorem one_rep_zero (n : Nat) (W : Tape) :
    cons true (rep n [false, true] (cons false W)) = rep (n + 1) [true, false] W := by
  have h := rep_rotate n [true] [false, true] [true, false] rfl (cons false W)
  simp only [app_cons, app_nil] at h
  rw [h, ← rep_app_comm]; rfl

theorem back_read (ys : List Nat) (y : Nat) (T : Tape) : ∀ n : Nat,
    cons true (rep n [false, true] (retR ys (cons false (cons true (cons true (cons false (rep y [true, false] T)))))))
      = rep (n + 1) [true, false] (encO (ys ++ [y]) T) := by
  induction ys with
  | nil => intro n; exact one_rep_zero n _
  | cons a ys ih =>
    intro n
    show cons true (rep n [false, true] (cons false (cons true (cons true (rep a [false, true] (retR ys _)))))) = _
    rw [one_rep_zero, ih]
    rfl

/-! ## One decrement -/

theorem len_le_sum (l : List Nat) : l.length ≤ (l.map (· + 1)).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp [List.map, List.sum_cons]; omega

/-- The tape at an event: `0 (10)^X`, then the bits and their blocks. -/
def encB : List (Bool × Nat) → Tape → Tape
  | [], R => R
  | (b, y) :: bl, R => cons b (rep y [true, false] (encB bl R))

def event (X : Nat) (bl : List (Bool × Nat)) (R : Tape) : Config := ⟨blank, cons false (rep X [true, false] (encB bl R)), .A⟩

theorem dec_core (X : Nat) (ys : List Nat) (z : Nat) (T : Tape) :
    steps (6 * X + 6 * (ys.map (· + 1)).sum + 10)
      ⟨blank, cons false (rep X [true, false] (encZ ys (cons true (rep (z + 1) [true, false] T)))), .A⟩ =
      some ⟨blank, cons false (rep (X + 2) [true, false] (encO ys (cons false (rep z [true, false] T)))), .A⟩ := by
  have h1 := u_start blank (rep X [true, false] (encZ ys (cons true (rep (z + 1) [true, false] T))))
  have h2 := cross_B_r_10 X (cons true blank) (encZ ys (cons true (rep (z + 1) [true, false] T)))
  have h3 := out_run ys (rep X [true, false] (cons true blank)) (cons true (rep (z + 1) [true, false] T))
  have h4 := u_turn (outL ys (rep X [true, false] (cons true blank))) (rep z [true, false] T)
  have h123 := steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 h4))
  rcases List.eq_nil_or_concat ys with e | ⟨ys', y, e⟩
  · subst e
    have h5 := cross_F_l_01 X (cons true blank) (cons false (rep z [true, false] T))
    have h6 := u_endF (rep X [true, false] (cons false (rep z [true, false] T)))
    exact steps_congr trans (by simp [sumO]; omega) (steps_seq trans h123 (steps_seq trans h5 h6))
  · subst e
    simp only [List.concat_eq_append] at h123 ⊢
    rw [outL_snoc] at h123
    have h5 := cross_F_l_01 y (cons true (cons true (cons true (outL ys' (rep X [true, false] (cons true blank))))))
      (cons false (rep z [true, false] T))
    have h6 := u_f111 (outL ys' (rep X [true, false] (cons true blank)))
      (rep y [true, false] (cons false (rep z [true, false] T)))
    have h7 := ret_run ys' (rep X [true, false] (cons true blank))
      (cons false (cons true (cons true (cons false (rep y [true, false] (cons false (rep z [true, false] T)))))))
    have h8 := cross_D_l_01 X (cons true blank)
      (retR ys' (cons false (cons true (cons true (cons false (rep y [true, false] (cons false (rep z [true, false] T))))))))
    have h9 := u_endD (rep X [false, true]
      (retR ys' (cons false (cons true (cons true (cons false (rep y [true, false] (cons false (rep z [true, false] T)))))))))
    have h := steps_seq trans h123 (steps_seq trans h5 (steps_seq trans h6 (steps_seq trans h7 (steps_seq trans h8 h9))))
    rw [back_read] at h
    have hs : ∀ l : List Nat, sumO l + 0 = 2 * (l.map (· + 1)).sum + l.length := by
      intro l; induction l with
      | nil => rfl
      | cons a l ih => simp [sumO, List.map, List.sum_cons] at ih ⊢; omega
    have hr : ∀ l : List Nat, sumR l = 4 * (l.map (· + 1)).sum - l.length := by
      intro l; induction l with
      | nil => rfl
      | cons a l ih =>
        simp [sumR, List.map, List.sum_cons] at ih ⊢
        have := len_le_sum l
        omega
    have e1 := hs (ys' ++ [y])
    have e2 := hr ys'
    have e3 := len_le_sum ys'
    simp [List.map_append, List.sum_append] at e1 ⊢
    exact steps_congr trans (by omega) h

/-! ## The counter -/

/-- The lowest set bit exists, and it and the zero bits below it have non-empty blocks. -/
def reg : List (Bool × Nat) → Bool
  | [] => false
  | (true, y) :: _ => decide (1 ≤ y)
  | (false, y) :: bl => decide (1 ≤ y) && reg bl

/-- One decrement of the bit list (lowest bit first), taking one copy from the block of the lowest set bit. -/
def dec1 : List (Bool × Nat) → List (Bool × Nat)
  | [] => []
  | (true, y) :: bl => (false, y - 1) :: bl
  | (false, y) :: bl => (true, y) :: dec1 bl

/-- The blocks of the zero bits below the lowest set bit. -/
def zsum : List (Bool × Nat) → Nat
  | [] => 0
  | (true, _) :: _ => 0
  | (false, y) :: bl => y + zsum bl

theorem reg_split : ∀ (bl : List (Bool × Nat)), reg bl = true → ∃ ys z rest,
    (∀ R, encB bl R = encZ ys (cons true (rep (z + 1) [true, false] (encB rest R)))) ∧
    (∀ R, encB (dec1 bl) R = encO ys (cons false (rep z [true, false] (encB rest R)))) ∧
    zsum bl = (ys.map (· + 1)).sum
  | [], h => by simp [reg] at h
  | (true, y) :: bl, h => by
    simp [reg] at h
    obtain ⟨z, rfl⟩ : ∃ z, y = z + 1 := ⟨y - 1, by omega⟩
    exact ⟨[], z, bl, fun R => rfl, fun R => by simp [dec1, encB, encO], by simp [zsum]⟩
  | (false, y) :: bl, h => by
    simp [reg] at h
    obtain ⟨ys, z, rest, e1, e2, e3⟩ := reg_split bl h.2
    obtain ⟨w, rfl⟩ : ∃ w, y = w + 1 := ⟨y - 1, by omega⟩
    refine ⟨w :: ys, z, rest, fun R => ?_, fun R => ?_, ?_⟩
    · simp only [encB, encZ, e1]
    · simp only [dec1, encB, encO, e2]
    · simp [zsum, e3, List.map, List.sum_cons]

/-- One decrement at the left end, for every bit list. -/
theorem dec_step (X : Nat) (bl : List (Bool × Nat)) (R : Tape) (h : reg bl = true) :
    steps (6 * X + 6 * zsum bl + 10) (event X bl R) = some (event (X + 2) (dec1 bl) R) := by
  obtain ⟨ys, z, rest, e1, e2, e3⟩ := reg_split bl h
  unfold event
  rw [e1, e2, e3]
  exact dec_core X ys z (encB rest R)

end H180268
