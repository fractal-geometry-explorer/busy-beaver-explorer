import Rules

/-!
# The regular macro step (Q-steps), for every word and every counter

A *Q configuration* `qc W a P T` is the tape

    W 0 1^(3a) B>0 0^(3p₁+2) 1 0^(3p₂+2) 1 … T

`W` is a word: blocks of 1s separated by single 0s, blank to its left, here listed **last block first**; `P` lists
the gaps of the counter right of the head as `p` with gap length `3p + 2`; `T` is any tape.  The theorems below
are the six Q-steps of `Rules.lean` restated on these configurations: between two Q events the machine applies the
map `phi` twice to the word and adds one to the counter.  `phi` removes the last block `b` and adds 2 to the block
before it, then appends `(b-1)/2` blocks of a single 1 (`phi` in this file works on the reversed list).
-/

namespace H114477

open TM

/-- A word, last block first, as the stream left of a separator: `b` ones, a 0, the rest. -/
def wl : List Nat → Tape
  | [] => blank
  | b :: W => rep b [true] (cons false (wl W))

/-- The counter's gaps `0^(3p+2) 1`, then the tape `T`. -/
def pt : List Nat → Tape → Tape
  | [], T => T
  | p :: P, T => cons false (cons false (rep p [false, false, false] (cons true (pt P T))))

/-- The Q configuration `W 0 1^(3a) B>0 R` with `R = pt P T`. -/
def qc (W : List Nat) (a : Nat) (P : List Nat) (T : Tape) : Config :=
  ⟨rep a [true, true, true] (cons false (wl W)), cons false (pt P T), .B⟩

/-- The word map on the reversed word: `[.., x, b] ↦ [.., x + 2, 1, …, 1]` with `(b - 1)/2` ones. -/
def phi : List Nat → List Nat
  | b :: x :: W => List.replicate ((b - 1) / 2) 1 ++ (x + 2) :: W
  | W => W

theorem rep_ones_odd (n : Nat) (s : Tape) : rep (2 * n + 1) [true] s = rep n [true, true] (cons true s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by omega, rep_succ, rep_succ, ih]; rfl

theorem rep_threes (n : Nat) (s : Tape) : rep (3 * n) [true] s = rep n [true, true, true] s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 3 * (n + 1) = 3 * n + 1 + 1 + 1 by omega, rep_succ, rep_succ, rep_succ, ih]; rfl

theorem wl_ones (j : Nat) (V : List Nat) : wl (List.replicate j 1 ++ V) = rep j [true, false] (wl V) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [List.replicate_succ, List.cons_append, wl, ih]; rfl

theorem sep_ones (j : Nat) (V : List Nat) :
    cons false (wl (List.replicate j 1 ++ V)) = rep j [false, true] (cons false (wl V)) := by
  rw [wl_ones]; exact rep_rotate j [false] [true, false] [false, true] rfl (wl V)

theorem wl_cons (b : Nat) (W : List Nat) : wl (b :: W) = rep b [true] (cons false (wl W)) := rfl

theorem wl_two (x : Nat) (V : List Nat) : wl ((x + 2) :: V) = cons true (cons true (wl (x :: V))) := by
  simp only [wl, rep_succ]; rfl

theorem phi2_big (j x : Nat) (V : List Nat) :
    phi (phi ((2 * j + 5) :: x :: V)) = 3 :: (List.replicate j 1 ++ (x + 2) :: V) := by
  simp only [phi, show (2 * j + 5 - 1) / 2 = j + 2 by omega, List.replicate_succ, List.cons_append]
  rfl

theorem phi2_three (x : Nat) (V : List Nat) : phi (phi (3 :: x :: V)) = (x + 4) :: V := by
  simp [phi]

theorem phi2_one (i y : Nat) (V : List Nat) :
    phi (phi (1 :: (2 * i + 1) :: y :: V)) = List.replicate (i + 1) 1 ++ (y + 2) :: V := by
  simp only [phi, show (1 - 1) / 2 = 0 by rfl, List.replicate_zero, List.nil_append,
    show (2 * i + 1 + 2 - 1) / 2 = i + 1 by omega]

/-- The counter after a wide step: a new unit of one, the old low part as a gap. -/
theorem pt_wide (a : Nat) (P : List Nat) (T : Tape) :
    cons false (pt (a :: P) T) = rep (a + 1) [false, false, false] (cons true (pt P T)) := rfl

/-- `t` gaps of length 2 in front of `R`. -/
theorem pt_units (t : Nat) (R : Tape) : pt (List.replicate t 0) R = rep t [false, false, true] R := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [List.replicate_succ, pt, ih]; rfl

/-- A gap of length `3(p+1)+2` is three 0s and a gap of length `3p+2`. -/
theorem pt_long (p : Nat) (P : List Nat) (T : Tape) :
    pt ((p + 1) :: P) T = cons false (cons false (cons false (pt (p :: P) T))) := rfl

theorem rep3_one (X : Tape) : rep 1 [true, true, true] X = cons true (cons true (cons true X)) := rfl

theorem rep3_more (t : Nat) (X : Tape) :
    rep (t + 2) [true, true, true] X = cons true (cons true (cons true (cons true (rep t [true, true, true]
      (cons true (cons true X)))))) := by
  rw [rep_succ, rep_succ]
  show cons true (cons true (cons true (cons true (cons true (cons true (rep t [true, true, true] X)))))) = _
  congr 4
  exact rep_rotate t [true, true] [true, true, true] [true, true, true] rfl X

/-! The six Q-steps on Q configurations.  `wide`: the low unit has `a + 2 ≥ 2` parts; `unit`: it has one part,
followed by `t` gaps of length 2 and then at least three 0s (`cons false (cons false (cons false R))`, which is how
both a longer gap and blank tape begin). -/

theorem qstep_big_wide (a j x : Nat) (V P : List Nat) (T : Tape) :
    steps (3 * a + 8 * j + 41) (qc ((2 * j + 5) :: x :: V) (a + 2) P T)
      = some (qc (phi (phi ((2 * j + 5) :: x :: V))) 1 (a :: P) T) := by
  have h := q_big_wide a j (wl (x :: V)) (pt P T)
  rw [phi2_big]
  simp only [qc, pt_wide]
  rw [wl_cons (2 * j + 5), show 2 * j + 5 = 2 * (j + 2) + 1 by omega, rep_ones_odd, wl_cons 3, sep_ones]
  exact h

theorem qstep_three_wide (a x : Nat) (V P : List Nat) (T : Tape) :
    steps (3 * a + 33) (qc (3 :: x :: V) (a + 2) P T) = some (qc (phi (phi (3 :: x :: V))) 1 (a :: P) T) := by
  have h := q_three_wide a (wl (x :: V)) (pt P T)
  rw [phi2_three]
  simp only [qc, pt_wide]
  exact h

theorem qstep_one_wide (a i y : Nat) (V P : List Nat) (T : Tape) :
    steps (3 * a + 8 * i + 33) (qc (1 :: (2 * i + 1) :: y :: V) (a + 2) P T)
      = some (qc (phi (phi (1 :: (2 * i + 1) :: y :: V))) 1 (a :: P) T) := by
  have h := q_one_wide a i (wl (y :: V)) (pt P T)
  rw [phi2_one]
  simp only [qc, pt_wide]
  rw [wl_cons 1, wl_cons (2 * i + 1), rep_ones_odd, wl_ones, ← rep_app_comm i [true, false]]
  exact h

theorem qstep_big_unit (t j x : Nat) (V : List Nat) (R : Tape) :
    steps (8 * j + 3 * t + 41) ⟨rep 1 [true, true, true] (cons false (wl ((2 * j + 5) :: x :: V))),
        cons false (pt (List.replicate t 0) (cons false (cons false (cons false R)))), .B⟩
      = some ⟨rep (t + 2) [true, true, true] (cons false (wl (phi (phi ((2 * j + 5) :: x :: V))))),
        cons false R, .B⟩ := by
  have h := q_big_unit j t (wl (x :: V)) R
  rw [phi2_big, pt_units, rep3_more]
  rw [wl_cons (2 * j + 5), show 2 * j + 5 = 2 * (j + 2) + 1 by omega, rep_ones_odd, wl_cons 3, sep_ones]
  exact h

theorem qstep_three_unit (t x : Nat) (V : List Nat) (R : Tape) :
    steps (3 * t + 33) ⟨rep 1 [true, true, true] (cons false (wl (3 :: x :: V))),
        cons false (pt (List.replicate t 0) (cons false (cons false (cons false R)))), .B⟩
      = some ⟨rep (t + 2) [true, true, true] (cons false (wl (phi (phi (3 :: x :: V))))), cons false R, .B⟩ := by
  have h := q_three_unit t (wl (x :: V)) R
  rw [phi2_three, pt_units, rep3_more]
  exact h

theorem qstep_one_unit (t i y : Nat) (V : List Nat) (R : Tape) :
    steps (8 * i + 3 * t + 33) ⟨rep 1 [true, true, true] (cons false (wl (1 :: (2 * i + 1) :: y :: V))),
        cons false (pt (List.replicate t 0) (cons false (cons false (cons false R)))), .B⟩
      = some ⟨rep (t + 2) [true, true, true] (cons false (wl (phi (phi (1 :: (2 * i + 1) :: y :: V))))),
        cons false R, .B⟩ := by
  have h := q_one_unit i t (wl (y :: V)) R
  rw [phi2_one, pt_units, rep3_more]
  rw [wl_cons 1, wl_cons (2 * i + 1), rep_ones_odd, wl_ones, ← rep_app_comm i [true, false]]
  exact h

end H114477
