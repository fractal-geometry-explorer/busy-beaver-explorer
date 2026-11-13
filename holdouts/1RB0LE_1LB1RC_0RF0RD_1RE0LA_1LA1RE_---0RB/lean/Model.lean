import Rules

/-!
# The block model, proved

`E S p q r` is the tape `0^inf 1^S_k 00 … 1^S_1 00 1^p 00 1^q 0 1^r E> 0^inf` (the stack `S` with its top `S_1`
next to `p`), and `P n` is `0^inf E> 0 0 1^n 0 1 0^inf`.  From the local rules of `Rules.lean` and two
crossing lemmas (proved by induction), every sweep of the block model is a theorem, with its exact step count.
-/

namespace H145825

open TM

theorem seqc {a n : Nat} {c : Config} {x : Option Config} (h : steps a c = x) (e : a = n) : steps n c = x := by
  subst e; exact h

theorem ones_succ (n : Nat) (t : Tape) : rep (n + 1) [true] t = cons true (rep n [true] t) := rfl

theorem ones_1 (t : Tape) : rep 1 [true] t = cons true t := rfl
theorem ones_2 (t : Tape) : rep 2 [true] t = cons true (cons true t) := rfl
theorem ones_3 (t : Tape) : rep 3 [true] t = cons true (cons true (cons true t)) := rfl

theorem ones_cons (n : Nat) (t : Tape) : rep n [true] (cons true t) = cons true (rep n [true] t) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ones_succ, ih]; rfl

/-- `E` moves the hole left through `k` ones. -/
theorem cross_l : ∀ (k : Nat) (L R : Tape),
    steps (3 * k) ⟨rep k [true] (cons true L), cons false R, .E⟩ = some ⟨cons true L, cons false (rep k [true] R), .E⟩ := by
  intro k
  induction k with
  | zero => intro L R; rfl
  | succ k ih =>
    intro L R
    have h1 := c_l (rep k [true] L) R
    have h2 := ih L (cons true R)
    simp only [ones_succ, ones_cons] at h1 h2 ⊢
    exact seqc (steps_seq trans h1 h2) (by omega)

/-- `B` moves right through `k` ones (followed by two more). -/
theorem cross_r : ∀ (k : Nat) (L R : Tape),
    steps (5 * k) ⟨L, rep k [true] (cons true (cons true R)), .B⟩ = some ⟨rep k [true] L, cons true (cons true R), .B⟩ := by
  intro k
  induction k with
  | zero => intro L R; rfl
  | succ k ih =>
    intro L R
    have h1 := c_r L (rep k [true] R)
    have h2 := ih (cons true L) R
    simp only [ones_succ, ones_cons] at h1 h2 ⊢
    exact seqc (steps_seq trans h1 h2) (by omega)

/-- The stack, top first. -/
def stk : List Nat → Tape
  | [] => blank
  | x :: S => cons false (cons false (rep x [true] (stk S)))

def E (S : List Nat) (p q r : Nat) : Config :=
  ⟨rep r [true] (cons false (rep q [true] (cons false (cons false (rep p [true] (stk S)))))), blank, .E⟩

def P (n : Nat) : Config := ⟨blank, cons false (cons false (rep n [true] (cons false (cons true blank)))), .E⟩

/-- One sweep with `q ≥ 4`: two 1s from `q` to `p`, one more on `r`. -/
theorem round (S : List Nat) (p q r : Nat) :
    steps (8 * q + 4 * r + 27) (E S (p + 1) (q + 4) (r + 1)) = some (E S (p + 3) (q + 2) (r + 2)) := by
  have h1 := cross_l r (cons false (rep (q + 4) [true] (cons false (cons false (rep (p + 1) [true] (stk S)))))) blank
  have h2 := r_hole (rep (q + 4) [true] (cons false (cons false (rep (p + 1) [true] (stk S))))) (rep r [true] blank)
  have h3 := cross_l (q + 3) (cons false (cons false (rep (p + 1) [true] (stk S))))
    (cons false (cons true (rep r [true] blank)))
  have h4 := r_turn (rep p [true] (stk S)) (rep q [true] (cons false (cons true (rep r [true] blank))))
  have h5 := cross_r q (cons true (cons false (cons false (cons true (cons true (cons true (rep p [true] (stk S))))))))
    (cons false (cons true (rep r [true] blank)))
  have h6 := r_back (r + 1) (rep q [true] (cons true (cons false (cons false (cons true (cons true (cons true
    (rep p [true] (stk S)))))))))
  simp only [ones_succ, ones_cons, cons_false_blank] at h1 h2 h3 h4 h5 h6
  simp only [E, ones_succ]
  have x1 := steps_seq trans h1 h2
  have x2 := steps_seq trans x1 h3
  have x3 := steps_seq trans x2 h4
  have x4 := steps_seq trans x3 h5
  have x5 := steps_seq trans x4 h6
  exact seqc x5 (by omega)

/-- `q = 3`. -/
theorem sweep_q3 (S : List Nat) (p r : Nat) :
    steps (4 * r + 19) (E S (p + 1) 3 (r + 1)) = some (E S (p + 3) 1 (r + 2)) := by
  have h1 := cross_l r (cons false (rep 3 [true] (cons false (cons false (rep (p + 1) [true] (stk S)))))) blank
  have h2 := r_q3 r (rep p [true] (stk S))
  simp only [ones_succ, ones_cons, cons_false_blank, rep_zero, ones_1, ones_2, ones_3] at h1 h2
  simp only [E, ones_succ, rep_zero, ones_1, ones_2, ones_3]
  exact seqc (steps_seq trans h1 h2) (by omega)

/-- `q = 2`, `r = 1`. -/
theorem sweep_q2r1 (S : List Nat) (p : Nat) :
    steps 31 (E S (p + 1) 2 1) = some (E S (p + 3) 3 1) := by
  have h := r_q2r1 (rep p [true] (stk S))
  simp only [E, ones_succ, rep_zero, ones_1, ones_2, ones_3]
  exact h

/-- `q = 2`, `r = 2`: the machine halts (20 steps, then F reads 0). -/
theorem sweep_halt (S : List Nat) (p : Nat) :
    ∃ c, steps 20 (E S (p + 1) 2 2) = some c ∧ step c = none := by
  have h1 := cross_l 1 (cons false (rep 2 [true] (cons false (cons false (rep (p + 1) [true] (stk S)))))) blank
  have h2 := r_halt (rep p [true] (stk S))
  simp only [ones_succ, ones_cons, cons_false_blank, rep_zero, ones_1, ones_2, ones_3] at h1 h2
  simp only [E, ones_succ, rep_zero, ones_1, ones_2, ones_3]
  exact ⟨_, seqc (steps_seq trans h1 h2) (by omega), rfl⟩

/-- `q = 2`, `r ≥ 3`: push `p + 2`. -/
theorem sweep_push (S : List Nat) (p r : Nat) :
    steps (8 * r + 24) (E S (p + 1) 2 (r + 3)) = some (E ((p + 3) :: S) 1 (r + 1) 1) := by
  have h1 := cross_l (r + 2) (cons false (rep 2 [true] (cons false (cons false (rep (p + 1) [true] (stk S)))))) blank
  have h2 := r_push r (rep p [true] (stk S))
  simp only [ones_succ, ones_cons, cons_false_blank, rep_zero, ones_1, ones_2, ones_3] at h1 h2
  simp only [E, stk, ones_succ, rep_zero, ones_1, ones_2, ones_3]
  exact seqc (steps_seq trans h1 h2) (by omega)

/-- `q = 1`: `p`, `q`, `r` merge into one block (the common part of the two pop rules). -/
theorem sweep_merge (T : Tape) (p r : Nat) :
    steps (8 * r + 30) ⟨rep (r + 1) [true] (cons false (rep 1 [true] (cons false (cons false (rep (p + 1) [true] T))))),
      blank, .E⟩ = some ⟨rep 1 [true] (cons false (rep (p + r + 6) [true] T)), blank, .E⟩ := by
  have h1 := cross_l r (cons false (rep 1 [true] (cons false (cons false (rep (p + 1) [true] T))))) blank
  have h2 := r_pop r (rep p [true] T)
  have h3 := cross_r (r + 3) (cons true (cons true (rep p [true] T))) blank
  have h4 := r_back 0 (rep (r + 3) [true] (cons true (cons true (rep p [true] T))))
  simp only [ones_succ, ones_cons, cons_false_blank, rep_zero, ones_1, ones_2, ones_3] at h1 h2 h3 h4
  simp only [ones_succ, rep_zero, ones_1]
  have e : rep (p + r) [true] T = rep r [true] (rep p [true] T) := by
    rw [Nat.add_comm, rep_add]
  rw [e]
  exact seqc (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 h4))) (by omega)

/-- `q = 1` with a block `x` on the stack: pop it. -/
theorem sweep_pop (x : Nat) (S : List Nat) (p r : Nat) :
    steps (8 * r + 30) (E (x :: S) (p + 1) 1 (r + 1)) = some (E S x (p + r + 6) 1) :=
  sweep_merge _ p r

/-- `q = 1` with an empty stack: one block is left, with `p = 0`. -/
theorem sweep_pop_nil (p r : Nat) :
    steps (8 * r + 30) (E [] (p + 1) 1 (r + 1)) = some (E [] 0 (p + r + 6) 1) := by
  have h := sweep_merge blank p r
  simp only [E, stk, rep_zero, cons_false_blank]
  simpa only [cons_false_blank] using h

/-- One block left: the head runs to the left end, `P (v + 1)`. -/
theorem to_P (v : Nat) : steps (3 * v + 4) (E [] 0 (v + 1) 1) = some (P (v + 1)) := by
  have h1 := r_hole (rep (v + 1) [true] blank) blank
  have h2 := cross_l v blank (cons false (cons true blank))
  have h3 := r_left (rep v [true] (cons false (cons true blank)))
  simp only [ones_succ, ones_cons, cons_false_blank, rep_zero, ones_1, ones_2, ones_3] at h1 h2 h3
  simp only [E, P, stk, ones_succ, ones_cons, rep_zero, cons_false_blank]
  exact seqc (steps_seq trans h1 (steps_seq trans h2 h3)) (by omega)

/-- From `P (n + 4)` the first sweep: `E [] 2 (n + 2) 2`. -/
theorem from_P (n : Nat) : steps (5 * n + 14) (P (n + 4)) = some (E [] 2 (n + 2) 2) := by
  have h1 := r_start (rep n [true] (cons false (cons true blank)))
  have h2 := cross_r n (cons true (cons false (cons false (cons true (cons true blank))))) (cons false (cons true blank))
  have h3 := r_back 1 (rep n [true] (cons true (cons false (cons false (cons true (cons true blank))))))
  simp only [ones_succ, ones_cons, cons_false_blank, rep_zero, ones_1, ones_2, ones_3] at h1 h2 h3
  simp only [E, P, stk, ones_succ, ones_cons, rep_zero, cons_false_blank]
  exact seqc (steps_seq trans h1 (steps_seq trans h2 h3)) (by omega)

end H145825
