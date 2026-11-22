import Machine

/-! # 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE: the eat visit of the right-end bouncer

Between visits to the right end the head sweeps left and comes back.  In one recurring phase the tape right of the
irregular digit list reads  L 1^(a+3) (01011)^b (011)^c 0  with the head in D on the blank cell after it, and the
sweep turns inside the block of 1s: it eats three 1s, crosses (01011)^b and (011)^c both ways (the left sweep turns
(011)^c into (001)^c, the right sweep turns it back) and appends two copies of 011.  So

  eat:       L 1^(a+3) (01011)^b (011)^c 0 D> 0^inf  reaches  L 1^a (01011)^b (011)^(c+2) 0 D> 0^inf
             in 20b + 10c + 25 steps (for every a, b, c and every tape L; L is never read),
  eat_iter:  k visits in a row take  k(20b + 10c + 15) + 10k^2  steps and leave  1^a (01011)^b (011)^(c+2k).

The phase lasts until the block of 1s is used up; it is seen in the run for example from step 3.1e8 to 3.84e8
(b = 1,379, a from about 5,000 down to 171).  The single visit is proved by `tools/py/bbtools/symtm.py` (rfl steps and
the crossing lemmas); the regrouping and the induction are written out below.

Written by the folder's `py/visit_rules.py` with `tools/py/bbtools/symtm.py`; do not edit by hand. -/

namespace H56722

open TM

/-- One eat visit, as the run writes the end configuration (proved by symtm). -/
theorem eat (a b c : Nat) (L : Tape) :
    steps (20 * b + 10 * c + 25) ⟨cons false (rep (c) [true, true, false] (rep (b) [true, true, false, true, false] (rep (a + 3) [true] (L)))), blank, .D⟩ = some ⟨cons false (cons true (cons true (cons false (rep (c) [true, true, false] (cons true (cons true (cons false (rep (b) [true, true, false, true, false] (rep (a) [true] (L)))))))))), blank, .D⟩ := by
  have hn : 5 + (0 + ((c) * 5 + (4 + ((b) * 7 + (5 + (0 + ((b) * 13 + (6 + (0 + ((c) * 5 + (5))))))))))) = 20 * b + 10 * c + 25 := by omega
  have h0 : steps 5 ⟨cons false (rep (c) [true, true, false] (rep (b) [true, true, false, true, false] (rep (a + 3) [true] (L)))), blank, .D⟩ = some ⟨cons true (cons false (rep (c) [true, true, false] (rep (b) [true, true, false, true, false] (rep (a + 3) [true] (L))))), cons true (cons true (blank)), .C⟩ := rfl
  have h1 : steps 0 ⟨cons true (cons false (rep (c) [true, true, false] (rep (b) [true, true, false, true, false] (rep (a + 3) [true] (L))))), cons true (cons true (blank)), .C⟩ = some ⟨rep (c) [true, false, true] (cons true (cons false (rep (b) [true, true, false, true, false] (rep (a + 3) [true] (L))))), cons true (cons true (blank)), .C⟩ := by
    simp only [steps_zero, show cons true (cons false (rep (c) [true, true, false] (rep (b) [true, true, false, true, false] (rep (a + 3) [true] (L))))) = rep (c) [true, false, true] (cons true (cons false (rep (b) [true, true, false, true, false] (rep (a + 3) [true] (L))))) from
      rep_rotate (c) [true, false] [true, true, false] [true, false, true] rfl (rep (b) [true, true, false, true, false] (rep (a + 3) [true] (L)))]
  have c2 : ∀ L R : Tape, steps 5 ⟨app [true, false, true] L, app [true] R, .C⟩ = some ⟨L, app [true] (app [true, false, false] R), .C⟩ := fun _ _ => rfl
  have h2 : steps ((c) * 5) ⟨rep (c) [true, false, true] (cons true (cons false (rep (b) [true, true, false, true, false] (rep (a + 3) [true] (L))))), cons true (cons true (blank)), .C⟩ = some ⟨cons true (cons false (rep (b) [true, true, false, true, false] (rep (a + 3) [true] (L)))), cons true (rep (c) [true, false, false] (cons true (blank))), .C⟩ :=
    cross_l trans c2 (c) (cons true (cons false (rep (b) [true, true, false, true, false] (rep (a + 3) [true] (L))))) (cons true (blank))
  have h3 : steps 4 ⟨cons true (cons false (rep (b) [true, true, false, true, false] (rep (a + 3) [true] (L)))), cons true (rep (c) [true, false, false] (cons true (blank))), .C⟩ = some ⟨rep (b) [true, true, false, true, false] (rep (a + 3) [true] (L)), cons false (cons false (cons false (rep (c) [true, false, false] (cons true (blank))))), .B⟩ := rfl
  have c4 : ∀ L R : Tape, steps 7 ⟨app [true, true, false, true, false] L, app [false] R, .B⟩ = some ⟨L, app [false] (app [true, true, false, false, true] R), .B⟩ := fun _ _ => rfl
  have h4 : steps ((b) * 7) ⟨rep (b) [true, true, false, true, false] (rep (a + 3) [true] (L)), cons false (cons false (cons false (rep (c) [true, false, false] (cons true (blank))))), .B⟩ = some ⟨rep (a + 3) [true] (L), cons false (rep (b) [true, true, false, false, true] (cons false (cons false (rep (c) [true, false, false] (cons true (blank)))))), .B⟩ :=
    cross_l trans c4 (b) (rep (a + 3) [true] (L)) (cons false (cons false (rep (c) [true, false, false] (cons true (blank)))))
  have h5 : steps 5 ⟨rep (a + 3) [true] (L), cons false (rep (b) [true, true, false, false, true] (cons false (cons false (rep (c) [true, false, false] (cons true (blank)))))), .B⟩ = some ⟨rep (a) [true] (L), cons true (cons false (cons false (cons true (rep (b) [true, true, false, false, true] (cons false (cons false (rep (c) [true, false, false] (cons true (blank))))))))), .B⟩ := rfl
  have h6 : steps 0 ⟨rep (a) [true] (L), cons true (cons false (cons false (cons true (rep (b) [true, true, false, false, true] (cons false (cons false (rep (c) [true, false, false] (cons true (blank))))))))), .B⟩ = some ⟨rep (a) [true] (L), rep (b) [true, false, false, true, true] (cons true (cons false (cons false (cons true (cons false (cons false (rep (c) [true, false, false] (cons true (blank))))))))), .B⟩ := by
    simp only [steps_zero, show cons true (cons false (cons false (cons true (rep (b) [true, true, false, false, true] (cons false (cons false (rep (c) [true, false, false] (cons true (blank))))))))) = rep (b) [true, false, false, true, true] (cons true (cons false (cons false (cons true (cons false (cons false (rep (c) [true, false, false] (cons true (blank))))))))) from
      rep_rotate (b) [true, false, false, true] [true, true, false, false, true] [true, false, false, true, true] rfl (cons false (cons false (rep (c) [true, false, false] (cons true (blank)))))]
  have c7 : ∀ L R : Tape, steps 13 ⟨app [] L, app [true, false, false, true, true] R, .B⟩ = some ⟨app [] (app [true, true, false, true, false] L), R, .B⟩ := fun _ _ => rfl
  have h7 : steps ((b) * 13) ⟨rep (a) [true] (L), rep (b) [true, false, false, true, true] (cons true (cons false (cons false (cons true (cons false (cons false (rep (c) [true, false, false] (cons true (blank))))))))), .B⟩ = some ⟨rep (b) [true, true, false, true, false] (rep (a) [true] (L)), cons true (cons false (cons false (cons true (cons false (cons false (rep (c) [true, false, false] (cons true (blank)))))))), .B⟩ :=
    cross_r trans c7 (b) (rep (a) [true] (L)) (cons true (cons false (cons false (cons true (cons false (cons false (rep (c) [true, false, false] (cons true (blank)))))))))
  have h8 : steps 6 ⟨rep (b) [true, true, false, true, false] (rep (a) [true] (L)), cons true (cons false (cons false (cons true (cons false (cons false (rep (c) [true, false, false] (cons true (blank)))))))), .B⟩ = some ⟨cons false (cons true (cons true (cons false (rep (b) [true, true, false, true, false] (rep (a) [true] (L)))))), cons false (cons false (rep (c) [true, false, false] (cons true (blank)))), .D⟩ := rfl
  have h9 : steps 0 ⟨cons false (cons true (cons true (cons false (rep (b) [true, true, false, true, false] (rep (a) [true] (L)))))), cons false (cons false (rep (c) [true, false, false] (cons true (blank)))), .D⟩ = some ⟨cons false (cons true (cons true (cons false (rep (b) [true, true, false, true, false] (rep (a) [true] (L)))))), rep (c) [false, false, true] (cons false (cons false (cons true (blank)))), .D⟩ := by
    simp only [steps_zero, show cons false (cons false (rep (c) [true, false, false] (cons true (blank)))) = rep (c) [false, false, true] (cons false (cons false (cons true (blank)))) from
      rep_rotate (c) [false, false] [true, false, false] [false, false, true] rfl (cons true (blank))]
  have c10 : ∀ L R : Tape, steps 5 ⟨app [false] L, app [false, false, true] R, .D⟩ = some ⟨app [false] (app [true, true, false] L), R, .D⟩ := fun _ _ => rfl
  have h10 : steps ((c) * 5) ⟨cons false (cons true (cons true (cons false (rep (b) [true, true, false, true, false] (rep (a) [true] (L)))))), rep (c) [false, false, true] (cons false (cons false (cons true (blank)))), .D⟩ = some ⟨cons false (rep (c) [true, true, false] (cons true (cons true (cons false (rep (b) [true, true, false, true, false] (rep (a) [true] (L))))))), cons false (cons false (cons true (blank))), .D⟩ :=
    cross_r trans c10 (c) (cons true (cons true (cons false (rep (b) [true, true, false, true, false] (rep (a) [true] (L)))))) (cons false (cons false (cons true (blank))))
  have h11 : steps 5 ⟨cons false (rep (c) [true, true, false] (cons true (cons true (cons false (rep (b) [true, true, false, true, false] (rep (a) [true] (L))))))), cons false (cons false (cons true (blank))), .D⟩ = some ⟨cons false (cons true (cons true (cons false (rep (c) [true, true, false] (cons true (cons true (cons false (rep (b) [true, true, false, true, false] (rep (a) [true] (L)))))))))), blank, .D⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (steps_seq trans h5 (steps_seq trans h6 (steps_seq trans h7 (steps_seq trans h8 (steps_seq trans h9 (steps_seq trans h10 (h11))))))))))))

/-- The three cells `0 1 1` next to the repeat, written on the left tape nearest first, are one more copy of it. -/
theorem w3_regroup (c : Nat) (X : Tape) :
    cons false (cons true (cons true (cons false (rep c [true, true, false]
      (cons true (cons true (cons false X))))))) = cons false (rep (c + 2) [true, true, false] X) := by
  show cons false (app [true, true, false] (rep c [true, true, false] (app [true, true, false] X))) = _
  rw [rep_app_comm]
  rfl

/-- One eat visit with the right end regrouped: `1^(a+3) (01011)^b (011)^c 0 D>` reaches `1^a (01011)^b (011)^(c+2) 0 D>`. -/
theorem eat_visit (a b c : Nat) (L : Tape) :
    steps (20 * b + 10 * c + 25)
      ⟨cons false (rep c [true, true, false] (rep b [true, true, false, true, false] (rep (a + 3) [true] L))), blank, .D⟩
    = some ⟨cons false (rep (c + 2) [true, true, false] (rep b [true, true, false, true, false] (rep a [true] L))), blank, .D⟩ := by
  have h := eat a b c L
  rw [w3_regroup] at h
  exact h

/-- Steps of `k` eat visits in a row starting with `(011)^c`. -/
def eatSteps (b : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, c => (20 * b + 10 * c + 25) + eatSteps b k (c + 2)

theorem eatSteps_eq (b : Nat) : ∀ k c, eatSteps b k c = k * (20 * b + 10 * c + 15) + 10 * (k * k) := by
  intro k
  induction k with
  | zero => intro c; simp [eatSteps]
  | succ k ih =>
    intro c
    rw [eatSteps, ih]
    simp only [Nat.succ_mul, Nat.mul_succ, Nat.mul_add]
    omega

/-- `k` eat visits in a row: `1^(a+3k) (01011)^b (011)^c 0 D>` reaches `1^a (01011)^b (011)^(c+2k) 0 D>` in
`k(20b + 10c + 15) + 10k²` steps, for every `a, b, c, k` and every tape `L` beyond the block of 1s. -/
theorem eat_iter (b : Nat) (L : Tape) : ∀ k a c,
    steps (k * (20 * b + 10 * c + 15) + 10 * (k * k))
      ⟨cons false (rep c [true, true, false] (rep b [true, true, false, true, false] (rep (a + 3 * k) [true] L))), blank, .D⟩
    = some ⟨cons false (rep (c + 2 * k) [true, true, false] (rep b [true, true, false, true, false] (rep a [true] L))), blank, .D⟩ := by
  intro k
  induction k with
  | zero => intro a c; simp
  | succ k ih =>
    intro a c
    rw [← eatSteps_eq, eatSteps, eatSteps_eq]
    have h1 := eat_visit (a + 3 * k) b c L
    rw [show a + 3 * k + 3 = a + 3 * (k + 1) by omega] at h1
    have h2 := ih a (c + 2)
    rw [show c + 2 + 2 * k = c + 2 * (k + 1) by omega] at h2
    exact TM.steps_seq trans h1 h2

end H56722
