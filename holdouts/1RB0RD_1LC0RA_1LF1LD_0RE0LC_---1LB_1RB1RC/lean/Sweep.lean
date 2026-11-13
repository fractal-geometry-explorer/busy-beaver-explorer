import Rules

/-!
# One sweep of 1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC is the carry automaton, for every digit string

An arrival is `0^inf (10)^m A> 1 1 x1 1 x2 1 ... xk 1 R`: the wall, then the counter x0 = 1, x1, ..., each digit
followed by a separator 1, then any tape R.  The carry automaton (README.md) is `carry`: states a, b, c, reading the
digits x1, x2, ...; `carry .a xs = some ys` when it stops inside xs, with ys the new digits (the rest unchanged).

`sweep`: if the carry stops inside xs, the arrival with wall m + 1 reaches the arrival with wall m + 2 and digits ys.
The proof chains the rules of `Rules.lean` (`fwd_*`, `stop*`, `back_*`, `back_end`) by induction over the digits:
on the way right the head is in state B, D or A (automaton state a, b, c) with the last pair still pending; on the
way back state C turns each pending pair into its digit.  Written by hand.
-/

namespace H74982

open TM

/-- The states of the carry automaton. -/
inductive Q where
  | a | b | c

/-- The carry: `none` if it runs off the end of the digits, else the new digits. -/
def carry : Q → List Bool → Option (List Bool)
  | _, [] => none
  | .a, false :: ds => some (true :: ds)
  | .a, true :: ds => (carry .b ds).map (false :: ·)
  | .b, false :: ds => (carry .a ds).map (true :: ·)
  | .b, true :: ds => (carry .c ds).map (false :: ·)
  | .c, false :: ds => (carry .c ds).map (false :: ·)
  | .c, true :: ds => (carry .a ds).map (true :: ·)

/-- Digits with their separators: `x1 1 x2 1 ... xk 1 R`. -/
def cells : List Bool → Tape → Tape
  | [], R => R
  | x :: xs, R => cons x (cons true (cells xs R))

/-- Pairs (w, t) left of the head, nearest first: `... w2 t2 w1 t1` with the head after t1. -/
def lt : List (Bool × Bool) → Tape → Tape
  | [], W => W
  | (w, t) :: ps, W => cons t (cons w (lt ps W))

/-- The wall of m pairs `10`, read from its right end. -/
abbrev wall (m : Nat) : Tape := rep m [false, true] blank

/-- An arrival: `0^inf (10)^m A> 1 1 (cells xs R)`. -/
def arrival (m : Nat) (xs : List Bool) (R : Tape) : Config :=
  ⟨wall m, cons true (cons true (cells xs R)), .A⟩

/-- The head going right in automaton state q, the last pair pending (`0 1`, `0 0`, `1 0` for a, b, c). -/
def fwd : Q → List (Bool × Bool) → Tape → Tape → Config
  | .a, ps, W, r => ⟨cons true (cons false (lt ps W)), r, .B⟩
  | .b, ps, W, r => ⟨cons false (cons false (lt ps W)), r, .D⟩
  | .c, ps, W, r => ⟨cons false (cons true (lt ps W)), r, .A⟩

/-- The head going back in state C on the separator of the pair p. -/
def back : Bool × Bool → List (Bool × Bool) → Tape → Tape → Config
  | (w, t), ps, W, r => ⟨cons w (lt ps W), cons t r, .C⟩

/-- The digit the previous pair stands for, when the carry is in state q. -/
def prev : Q → Bool
  | .a => true
  | .b => false
  | .c => false

theorem back_step (p : Bool × Bool) (hp : p ≠ (false, false)) (q : Bool × Bool) (ps : List (Bool × Bool))
    (W r : Tape) : ∃ s, steps s (back p (q :: ps) W r) =
      some (back q ps W (cons (decide (p = (false, true))) (cons true r))) := by
  obtain ⟨w, t⟩ := p
  obtain ⟨w2, t2⟩ := q
  cases w <;> cases t <;> cases t2
  · exact absurd rfl hp
  · exact absurd rfl hp
  · exact ⟨_, back_01_0 (cons w2 (lt ps W)) r⟩
  · exact ⟨_, back_01_1 (cons w2 (lt ps W)) r⟩
  · exact ⟨_, back_10_0 (cons w2 (lt ps W)) r⟩
  · exact ⟨_, back_10_1 (cons w2 (lt ps W)) r⟩
  · exact ⟨_, back_11_0 (cons w2 (lt ps W)) r⟩
  · exact ⟨_, back_11_1 (cons w2 (lt ps W)) r⟩

theorem stop_step (q : Bool × Bool) (ps : List (Bool × Bool)) (W R : Tape) :
    ∃ s, steps s (fwd .a (q :: ps) W (cons false (cons true R))) =
      some (back q ps W (cons true (cons true (cons true (cons true R))))) := by
  obtain ⟨w2, t2⟩ := q
  cases t2
  · exact ⟨_, stop0 (cons w2 (lt ps W)) R⟩
  · exact ⟨_, stop1 (cons w2 (lt ps W)) R⟩

/-- The carry from state q, pending pair on top of p :: ps: right, then back to the pair p. -/
theorem run (q : Q) (xs ys : List Bool) (h : carry q xs = some ys) (p : Bool × Bool) (ps : List (Bool × Bool))
    (W R : Tape) : ∃ s, steps s (fwd q (p :: ps) W (cells xs R)) =
      some (back p ps W (cons (prev q) (cons true (cells ys R)))) := by
  induction xs generalizing q ys p ps with
  | nil => cases q <;> simp [carry] at h
  | cons d ds ih =>
    cases q <;> cases d
    · -- a, 0: stop
      simp only [carry, Option.some.injEq] at h
      subst h
      exact stop_step p ps W (cells ds R)
    · -- a, 1
      simp only [carry, Option.map_eq_some_iff] at h
      obtain ⟨ys', h', rfl⟩ := h
      have h1 := fwd_a1 (cons true (cons false (lt (p :: ps) W))) (cells ds R)
      obtain ⟨s2, h2⟩ := ih .b ys' h' (false, true) (p :: ps)
      obtain ⟨s3, h3⟩ := back_step (false, true) (by decide) p ps W (cons false (cons true (cells ys' R)))
      exact ⟨_, steps_seq trans h1 (steps_seq trans h2 h3)⟩
    · -- b, 0
      simp only [carry, Option.map_eq_some_iff] at h
      obtain ⟨ys', h', rfl⟩ := h
      have h1 := fwd_b0 (lt (p :: ps) W) (cells ds R)
      obtain ⟨s2, h2⟩ := ih .a ys' h' (true, true) (p :: ps)
      obtain ⟨s3, h3⟩ := back_step (true, true) (by decide) p ps W (cons true (cons true (cells ys' R)))
      exact ⟨_, steps_seq trans h1 (steps_seq trans h2 h3)⟩
    · -- b, 1
      simp only [carry, Option.map_eq_some_iff] at h
      obtain ⟨ys', h', rfl⟩ := h
      have h1 := fwd_b1 (lt (p :: ps) W) (cells ds R)
      obtain ⟨s2, h2⟩ := ih .c ys' h' (true, false) (p :: ps)
      obtain ⟨s3, h3⟩ := back_step (true, false) (by decide) p ps W (cons false (cons true (cells ys' R)))
      exact ⟨_, steps_seq trans h1 (steps_seq trans h2 h3)⟩
    · -- c, 0
      simp only [carry, Option.map_eq_some_iff] at h
      obtain ⟨ys', h', rfl⟩ := h
      have h1 := fwd_c0 (cons false (cons true (lt (p :: ps) W))) (cells ds R)
      obtain ⟨s2, h2⟩ := ih .c ys' h' (true, false) (p :: ps)
      obtain ⟨s3, h3⟩ := back_step (true, false) (by decide) p ps W (cons false (cons true (cells ys' R)))
      exact ⟨_, steps_seq trans h1 (steps_seq trans h2 h3)⟩
    · -- c, 1
      simp only [carry, Option.map_eq_some_iff] at h
      obtain ⟨ys', h', rfl⟩ := h
      have h1 := fwd_c1 (lt (p :: ps) W) (cells ds R)
      obtain ⟨s2, h2⟩ := ih .a ys' h' (true, true) (p :: ps)
      obtain ⟨s3, h3⟩ := back_step (true, true) (by decide) p ps W (cons true (cons true (cells ys' R)))
      exact ⟨_, steps_seq trans h1 (steps_seq trans h2 h3)⟩

theorem wall_snoc (n : Nat) : cons false (cons true (rep n [false, true] (cons false (cons true blank)))) =
    wall (n + 2) := by
  have h : rep n [false, true] (cons false (cons true blank)) = rep (n + 1) [false, true] blank :=
    rep_app_comm n [false, true] blank
  rw [h]
  rfl

/-- One sweep is one step of the carry automaton (from state a on x1, x2, ...), for every digit string on which
the carry stops; the wall grows by one pair. -/
theorem sweep (n : Nat) (xs ys : List Bool) (h : carry .a xs = some ys) (R : Tape) :
    ∃ s, steps s (arrival (n + 1) xs R) = some (arrival (n + 2) ys R) := by
  have h1 := fwd_c1 (wall n) (cells xs R)
  obtain ⟨s2, h2⟩ := run .a xs ys h (true, true) [] (wall n) R
  have h3 := back_end n (cells ys R)
  rw [wall_snoc] at h3
  exact ⟨_, steps_seq trans h1 (steps_seq trans h2 h3)⟩

end H74982
