import Rules

/-!
# 1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_1RA0RE: a whole round when the first block has odd length

At the left end, in state E, the tape is blocks of ones separated by single 0s: `E> 0 1^x 0 1^a 0 1^b ...`.  Here the
odd first blocks give the simple rounds (in the twin 1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_0RA0LA it is the even ones):
the first two ones become a pair of 0s that the sweep pushes right, leaving `1 0` pairs behind (`sweep`); at the
end of the odd block the pair becomes a glider that crosses the second block and moves the next hole 3 cells left
(`endodd`); then every two pairs make another glider (`gliders`), and the round ends with E at the left end.
In block terms: [4K+3, a, b, ...] → [a+K, 3K+6+b, ...] (`round_mod3`) and [4K+1, a, b, ...] → [a+K-1, 3K+6+b, ...]
(`round_mod1`).
-/

namespace H25624

open TM

/-- The sweep: `L A> 0 0 (11)^n 1 R` becomes `L (10)^n A> 0 0 1 R` in 6n steps. -/
theorem sweep (n : Nat) : ∀ L R : Tape,
    steps (6 * n) ⟨L, cons false (cons false (rep n [true, true] (cons true R))), .A⟩ =
      some ⟨rep n [false, true] L, cons false (cons false (cons true R)), .A⟩ := by
  induction n with
  | zero => intro L R; rfl
  | succ n ih =>
    intro L R
    have h1 := ih L (cons true (cons true R))
    have e : rep (n + 1) [true, true] (cons true R) = rep n [true, true] (cons true (cons true (cons true R))) := by
      rw [← rep_app_comm]; rfl
    rw [e, show 6 * (n + 1) = 6 * n + 6 by omega]
    exact steps_seq trans h1 (pair (rep n [false, true] L) R)

/-- `1 (11)^n` is `(11)^n 1`. -/
theorem one_rep (n : Nat) : ∀ X : Tape, cons true (rep n [true, true] X) = rep n [true, true] (cons true X) := by
  induction n with
  | zero => intro X; rfl
  | succ n ih =>
    intro X
    show cons true (cons true (cons true (rep n [true, true] X))) =
      cons true (cons true (rep n [true, true] (cons true X)))
    rw [ih]

/-- `n` copies of `111` are `3n` ones. -/
theorem rep_three (n : Nat) (S : Tape) : rep (3 * n) [true] S = rep n [true, true, true] S := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show 3 * (n + 1) = 3 * n + 1 + 1 + 1 by omega]; simp only [rep_succ, ih]; rfl

/-- `j` gliders in a row: `L 1 0 (10)^(2j) 1 E> 0 1^(p+2) 0 1 R` becomes `L 1 0 1 E> 0 1^(p+2+j) 0 1 (111)^j R`. -/
theorem gliders (X : Tape) (j : Nat) : ∀ (p : Nat) (R : Tape), ∃ n,
    steps n ⟨cons true (rep (2 * j) [false, true] X), cons false (rep (p + 2) [true] (cons false (cons true R))), .E⟩ =
      some ⟨cons true X, cons false (rep (p + 2 + j) [true] (cons false (cons true (rep j [true, true, true] R)))), .E⟩ := by
  induction j with
  | zero => intro p R; exact ⟨0, by simp [steps]⟩
  | succ j ih =>
    intro p R
    have h1 := cycle p (rep (2 * j) [false, true] X) R
    have e1 : rep (2 * (j + 1)) [false, true] X =
        cons false (cons true (cons false (cons true (rep (2 * j) [false, true] X)))) := by
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega]; rfl
    have e2 : cons true (cons true (cons true (rep p [true]
        (cons false (cons true (cons true (cons true (cons true R)))))))) =
        rep (p + 1 + 2) [true] (cons false (cons true (app [true, true, true] R))) := rfl
    rw [e2] at h1
    obtain ⟨n, h2⟩ := ih (p + 1) (app [true, true, true] R)
    rw [rep_app_comm, show p + 1 + 2 + j = p + 2 + (j + 1) by omega] at h2
    exact ⟨_, by rw [e1]; exact steps_seq trans h1 h2⟩

/-- A round from a first block of length `4k + 3` (second block `a + 3`, third block starting with a 1):
`E> 0 1^(4k+3) 0 1^(a+3) 0 1 R` at the left end becomes `E> 0 1^(a+k+3) 0 1^(3k+7) R`, again at the left end. -/
theorem round_mod3 (k a : Nat) (R : Tape) : ∃ n,
    steps n ⟨blank, cons false (rep (4 * k + 3) [true] (cons false (rep (a + 3) [true] (cons false (cons true R))))), .E⟩ =
      some ⟨blank, cons false (rep (a + k + 3) [true] (cons false (rep (3 * k + 7) [true] R))), .E⟩ := by
  have e0 : rep (4 * k + 3) [true] (cons false (rep (a + 3) [true] (cons false (cons true R)))) =
      cons true (cons true (cons true (rep (2 * k) [true, true] (cons false (rep (a + 3) [true]
        (cons false (cons true R))))))) := by
    have r2 : ∀ (n : Nat) (S : Tape), rep (2 * n) [true] S = rep n [true, true] S := by
      intro n; induction n with
      | zero => intro S; rfl
      | succ n ih => intro S; rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]; simp only [rep_succ, ih]; rfl
    rw [show 4 * k + 3 = 3 + 2 * (2 * k) by omega, rep_add, r2]; rfl
  rw [e0]
  have h0 := start (rep (2 * k) [true, true] (cons false (rep (a + 3) [true] (cons false (cons true R)))))
  have h1 := sweep (2 * k) (cons false (cons true blank)) (cons false (rep (a + 3) [true] (cons false (cons true R))))
  rw [← one_rep] at h1
  have h2 := endodd a (rep (2 * k) [false, true] (cons false (cons true blank))) R
  have e2 : cons true (cons true (rep a [true] (cons false (cons true (cons true (cons true (cons true R))))))) =
      rep (a + 2) [true] (cons false (cons true (app [true, true, true] R))) := rfl
  rw [e2] at h2
  obtain ⟨n3, h3⟩ := gliders (cons false (cons true blank)) k a (app [true, true, true] R)
  have h4 := last (a + k) (rep k [true, true, true] (app [true, true, true] R))
  rw [show a + 2 + k = a + k + 2 by omega] at h3
  have e4 : cons false (cons true (cons true (cons true (rep (a + k) [true] (cons false (cons true (cons true
      (cons true (cons true (rep k [true, true, true] (app [true, true, true] R))))))))))) =
      cons false (rep (a + k + 3) [true] (cons false (rep (3 * k + 7) [true] R))) := by
    rw [← rep_three]
    show cons false (rep 3 [true] (rep (a + k) [true] (cons false (rep 4 [true] (rep (3 * k) [true]
      (rep 3 [true] R)))))) = _
    rw [← rep_add 3 (a + k), ← rep_add (3 * k) 3, ← rep_add 4 (3 * k + 3),
      show 3 + (a + k) = a + k + 3 by omega, show 4 + (3 * k + 3) = 3 * k + 7 by omega]
  rw [e4] at h4
  exact ⟨_, steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 h4)))⟩

/-- A round from a first block of length `4k + 5` (second block `a + 5`, third block starting with a 1):
`E> 0 1^(4k+5) 0 1^(a+5) 0 1 R` at the left end becomes `E> 0 1^(a+k+5) 0 1^(3k+10) R`, again at the left end. -/
theorem round_mod1 (k a : Nat) (R : Tape) : ∃ n,
    steps n ⟨blank, cons false (rep (4 * k + 5) [true] (cons false (rep (a + 5) [true] (cons false (cons true R))))), .E⟩ =
      some ⟨blank, cons false (rep (a + k + 5) [true] (cons false (rep (3 * k + 10) [true] R))), .E⟩ := by
  have e0 : rep (4 * k + 5) [true] (cons false (rep (a + 5) [true] (cons false (cons true R)))) =
      cons true (cons true (cons true (rep (2 * k + 1) [true, true] (cons false (rep (a + 2 + 3) [true]
        (cons false (cons true R))))))) := by
    have r2 : ∀ (n : Nat) (S : Tape), rep (2 * n) [true] S = rep n [true, true] S := by
      intro n; induction n with
      | zero => intro S; rfl
      | succ n ih => intro S; rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]; simp only [rep_succ, ih]; rfl
    rw [show 4 * k + 5 = 3 + 2 * (2 * k + 1) by omega, rep_add, r2]; rfl
  rw [e0]
  have h0 := start (rep (2 * k + 1) [true, true] (cons false (rep (a + 2 + 3) [true] (cons false (cons true R)))))
  have h1 := sweep (2 * k + 1) (cons false (cons true blank)) (cons false (rep (a + 2 + 3) [true] (cons false (cons true R))))
  rw [← one_rep] at h1
  have h2 := endodd (a + 2) (rep (2 * k + 1) [false, true] (cons false (cons true blank))) R
  have e2 : cons true (cons true (rep (a + 2) [true] (cons false (cons true (cons true (cons true (cons true R))))))) =
      rep (a + 2 + 2) [true] (cons false (cons true (app [true, true, true] R))) := rfl
  have e2' : rep (2 * k + 1) [false, true] (cons false (cons true blank)) =
      rep (2 * k) [false, true] (cons false (cons true (cons false (cons true blank)))) := by
    rw [rep_add]; rfl
  rw [e2] at h2
  rw [e2'] at h2
  obtain ⟨n3, h3⟩ := gliders (cons false (cons true (cons false (cons true blank)))) k (a + 2) (app [true, true, true] R)
  have h4 := last2 (a + k) (rep k [true, true, true] (app [true, true, true] R))
  rw [show a + 2 + 2 + k = a + k + 4 by omega] at h3
  have e4 : cons false (cons true (cons true (cons true (cons true (cons true (rep (a + k) [true] (cons false (cons true
      (cons true (cons true (cons true (cons true (cons true (cons true (rep k [true, true, true]
      (app [true, true, true] R)))))))))))))))) =
      cons false (rep (a + k + 5) [true] (cons false (rep (3 * k + 10) [true] R))) := by
    rw [← rep_three]
    show cons false (rep 5 [true] (rep (a + k) [true] (cons false (rep 7 [true] (rep (3 * k) [true]
      (rep 3 [true] R)))))) = _
    rw [← rep_add 5 (a + k), ← rep_add (3 * k) 3, ← rep_add 7 (3 * k + 3),
      show 5 + (a + k) = a + k + 5 by omega, show 7 + (3 * k + 3) = 3 * k + 10 by omega]
  rw [e4] at h4
  rw [e2'] at h1
  exact ⟨_, steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 h4)))⟩

end H25624
