import Machine

/-! # 1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB: one round of every event

Written by `py/event_rules.py` with `bbtools.symtm` (a symbolic run, its trace checked by the kernel); every count, every tape L, R. -/

namespace H170561

open TM

/-- An odd block of 2j+3 ones left of the head: two of its 1s go, the 0 on its left becomes 1 and three 1s are written after the head (they join the block to the right). -/
theorem r_odd (j : Nat) (L R : Tape) :
    steps (12 * j + 13) ⟨rep (j + 1) [true, true] (cons true (cons false (L))), cons false (R), .D⟩ = some ⟨cons true (rep (j) [true, true] (L)), cons false (cons true (cons true (cons true (R)))), .D⟩ := by
  have h0 : steps 2 ⟨rep (j + 1) [true, true] (cons true (cons false (L))), cons false (R), .D⟩ = some ⟨rep (j) [true, true] (cons true (cons false (L))), cons true (cons false (cons false (R))), .A⟩ := rfl
  have c1 : ∀ L R : Tape, steps 2 ⟨app [true, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, true] R), .A⟩ := fun _ _ => rfl
  have h1 : steps ((j) * 2) ⟨rep (j) [true, true] (cons true (cons false (L))), cons true (cons false (cons false (R))), .A⟩ = some ⟨cons true (cons false (L)), cons true (rep (j) [true, true] (cons false (cons false (R)))), .A⟩ :=
    cross_l trans c1 (j) (cons true (cons false (L))) (cons false (cons false (R)))
  have h2 : steps 0 ⟨cons true (cons false (L)), cons true (rep (j) [true, true] (cons false (cons false (R)))), .A⟩ = some ⟨cons true (cons false (L)), rep (j) [true, true] (cons true (cons false (cons false (R)))), .A⟩ := by
    simp only [steps_zero, show cons true (rep (j) [true, true] (cons false (cons false (R)))) = rep (j) [true, true] (cons true (cons false (cons false (R)))) from
      rep_rotate (j) [true] [true, true] [true, true] rfl (cons false (cons false (R)))]
  have c3 : ∀ L R : Tape, steps 10 ⟨app [true, false] L, app [true, true] R, .A⟩ = some ⟨app [true, false] (app [true, true] L), R, .A⟩ := fun _ _ => rfl
  have h3 : steps ((j) * 10) ⟨cons true (cons false (L)), rep (j) [true, true] (cons true (cons false (cons false (R)))), .A⟩ = some ⟨cons true (cons false (rep (j) [true, true] (L))), cons true (cons false (cons false (R))), .A⟩ :=
    cross_r trans c3 (j) (L) (cons true (cons false (cons false (R))))
  have h4 : steps 11 ⟨cons true (cons false (rep (j) [true, true] (L))), cons true (cons false (cons false (R))), .A⟩ = some ⟨cons true (rep (j) [true, true] (L)), cons false (cons true (cons true (cons true (R)))), .D⟩ := rfl
  exact steps_congr trans (a := 2 + ((j) * 2 + (0 + ((j) * 10 + (11))))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

/-- An even block of 2j+2 ones left of the head: the head erases its last 1 and comes to rest on the 0 on its left. -/
theorem r_shift (j : Nat) (L R : Tape) :
    steps (2 * j + 3) ⟨rep (j + 1) [true, true] (cons false (L)), cons false (R), .D⟩ = some ⟨L, cons false (cons true (rep (j) [true, true] (cons false (cons false (R))))), .D⟩ := by
  have h0 : steps 2 ⟨rep (j + 1) [true, true] (cons false (L)), cons false (R), .D⟩ = some ⟨rep (j) [true, true] (cons false (L)), cons true (cons false (cons false (R))), .A⟩ := rfl
  have c1 : ∀ L R : Tape, steps 2 ⟨app [true, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, true] R), .A⟩ := fun _ _ => rfl
  have h1 : steps ((j) * 2) ⟨rep (j) [true, true] (cons false (L)), cons true (cons false (cons false (R))), .A⟩ = some ⟨cons false (L), cons true (rep (j) [true, true] (cons false (cons false (R)))), .A⟩ :=
    cross_l trans c1 (j) (cons false (L)) (cons false (cons false (R)))
  have h2 : steps 1 ⟨cons false (L), cons true (rep (j) [true, true] (cons false (cons false (R)))), .A⟩ = some ⟨L, cons false (cons true (rep (j) [true, true] (cons false (cons false (R))))), .D⟩ := rfl
  exact steps_congr trans (a := 2 + ((j) * 2 + (1))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (h2)))

/-- An even block of 2j+4 ones with two 0s on its left: one 1 is written before the two 0s, the block loses four 1s and three 1s are written after the head. -/
theorem r_split (j : Nat) (L R : Tape) :
    steps (12 * j + 17) ⟨rep (j + 2) [true, true] (cons false (cons false (L))), cons false (R), .D⟩ = some ⟨rep (j) [true, true] (cons false (cons false (cons true (L)))), cons false (cons true (cons true (cons true (R)))), .D⟩ := by
  have h0 : steps 2 ⟨rep (j + 2) [true, true] (cons false (cons false (L))), cons false (R), .D⟩ = some ⟨rep (j + 1) [true, true] (cons false (cons false (L))), cons true (cons false (cons false (R))), .A⟩ := rfl
  have c1 : ∀ L R : Tape, steps 2 ⟨app [true, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, true] R), .A⟩ := fun _ _ => rfl
  have h1 : steps ((j + 1) * 2) ⟨rep (j + 1) [true, true] (cons false (cons false (L))), cons true (cons false (cons false (R))), .A⟩ = some ⟨cons false (cons false (L)), cons true (rep (j + 1) [true, true] (cons false (cons false (R)))), .A⟩ :=
    cross_l trans c1 (j + 1) (cons false (cons false (L))) (cons false (cons false (R)))
  have h2 : steps 7 ⟨cons false (cons false (L)), cons true (rep (j + 1) [true, true] (cons false (cons false (R)))), .A⟩ = some ⟨cons true (cons false (cons false (cons false (cons true (L))))), rep (j) [true, true] (cons false (cons false (R))), .A⟩ := rfl
  have c3 : ∀ L R : Tape, steps 10 ⟨app [true, false] L, app [true, true] R, .A⟩ = some ⟨app [true, false] (app [true, true] L), R, .A⟩ := fun _ _ => rfl
  have h3 : steps ((j) * 10) ⟨cons true (cons false (cons false (cons false (cons true (L))))), rep (j) [true, true] (cons false (cons false (R))), .A⟩ = some ⟨cons true (cons false (rep (j) [true, true] (cons false (cons false (cons true (L)))))), cons false (cons false (R)), .A⟩ :=
    cross_r trans c3 (j) (cons false (cons false (cons true (L)))) (cons false (cons false (R)))
  have h4 : steps 6 ⟨cons true (cons false (rep (j) [true, true] (cons false (cons false (cons true (L)))))), cons false (cons false (R)), .A⟩ = some ⟨rep (j) [true, true] (cons false (cons false (cons true (L)))), cons false (cons true (cons true (cons true (R)))), .D⟩ := rfl
  exact steps_congr trans (a := 2 + ((j + 1) * 2 + (7 + ((j) * 10 + (6))))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

/-- No block left of the head (a 0): the block of k+3 ones on the right gives one 1 to the left, moves left and the head ends right of it behind a carrier `0 1`. -/
theorem r_zero (k : Nat) (L R : Tape) :
    steps (5 * k + 6) ⟨cons false (L), cons false (cons true (cons true (cons true (rep (k) [true] (R))))), .D⟩ = some ⟨cons true (cons false (rep (k) [true] (cons false (cons false (cons true (L)))))), R, .A⟩ := by
  have h0 : steps 6 ⟨cons false (L), cons false (cons true (cons true (cons true (rep (k) [true] (R))))), .D⟩ = some ⟨cons true (cons false (cons false (cons false (cons true (L))))), rep (k) [true] (R), .A⟩ := rfl
  have c1 : ∀ L R : Tape, steps 5 ⟨app [true, false] L, app [true] R, .A⟩ = some ⟨app [true, false] (app [true] L), R, .A⟩ := fun _ _ => rfl
  have h1 : steps ((k) * 5) ⟨cons true (cons false (cons false (cons false (cons true (L))))), rep (k) [true] (R), .A⟩ = some ⟨cons true (cons false (rep (k) [true] (cons false (cons false (cons true (L)))))), R, .A⟩ :=
    cross_r trans c1 (k) (cons false (cons false (cons true (L)))) (R)
  exact steps_congr trans (a := 6 + ((k) * 5)) (by omega) (steps_seq trans h0 (h1))

/-- A block of exactly two 1s with two 0s on its left: it is erased, one 1 goes left, and the head crosses the block on the right. -/
theorem r_two (k : Nat) (L R : Tape) :
    steps (5 * k + 15) ⟨cons true (cons true (cons false (cons false (L)))), cons false (cons true (cons true (rep (k) [true] (R)))), .D⟩ = some ⟨cons true (cons false (rep (k) [true] (cons false (cons false (cons false (cons false (cons true (L)))))))), R, .A⟩ := by
  have h0 : steps 15 ⟨cons true (cons true (cons false (cons false (L)))), cons false (cons true (cons true (rep (k) [true] (R)))), .D⟩ = some ⟨cons true (cons false (cons false (cons false (cons false (cons false (cons true (L))))))), rep (k) [true] (R), .A⟩ := rfl
  have c1 : ∀ L R : Tape, steps 5 ⟨app [true, false] L, app [true] R, .A⟩ = some ⟨app [true, false] (app [true] L), R, .A⟩ := fun _ _ => rfl
  have h1 : steps ((k) * 5) ⟨cons true (cons false (cons false (cons false (cons false (cons false (cons true (L))))))), rep (k) [true] (R), .A⟩ = some ⟨cons true (cons false (rep (k) [true] (cons false (cons false (cons false (cons false (cons true (L)))))))), R, .A⟩ :=
    cross_r trans c1 (k) (cons false (cons false (cons false (cons false (cons true (L)))))) (R)
  exact steps_congr trans (a := 15 + ((k) * 5)) (by omega) (steps_seq trans h0 (h1))

/-- A single 1 with two 0s on its left. -/
theorem r_one (k : Nat) (L R : Tape) :
    steps (5 * k + 13) ⟨cons true (cons false (cons false (L))), cons false (cons true (cons true (rep (k) [true] (R)))), .D⟩ = some ⟨cons true (cons false (rep (k) [true] (cons true (cons true (cons false (cons true (L))))))), R, .A⟩ := by
  have h0 : steps 13 ⟨cons true (cons false (cons false (L))), cons false (cons true (cons true (rep (k) [true] (R)))), .D⟩ = some ⟨cons true (cons false (cons true (cons true (cons false (cons true (L)))))), rep (k) [true] (R), .A⟩ := rfl
  have c1 : ∀ L R : Tape, steps 5 ⟨app [true, false] L, app [true] R, .A⟩ = some ⟨app [true, false] (app [true] L), R, .A⟩ := fun _ _ => rfl
  have h1 : steps ((k) * 5) ⟨cons true (cons false (cons true (cons true (cons false (cons true (L)))))), rep (k) [true] (R), .A⟩ = some ⟨cons true (cons false (rep (k) [true] (cons true (cons true (cons false (cons true (L))))))), R, .A⟩ :=
    cross_r trans c1 (k) (cons true (cons true (cons false (cons true (L))))) (R)
  exact steps_congr trans (a := 13 + ((k) * 5)) (by omega) (steps_seq trans h0 (h1))

/-- A single 1 with an even block of 2j+2 ones behind one 0 on its left. -/
theorem r_oneE (j k : Nat) (L R : Tape) :
    steps (12 * j + 5 * k + 25) ⟨cons true (cons false (rep (j + 1) [true, true] (cons false (L)))), cons false (cons true (cons true (rep (k) [true] (R)))), .D⟩ = some ⟨cons true (cons false (rep (k) [true] (cons true (cons true (cons false (cons true (rep (j + 1) [true, true] (L)))))))), R, .A⟩ := by
  have h0 : steps 5 ⟨cons true (cons false (rep (j + 1) [true, true] (cons false (L)))), cons false (cons true (cons true (rep (k) [true] (R)))), .D⟩ = some ⟨cons true (rep (j + 1) [true, true] (cons false (L))), cons true (cons false (cons true (cons true (rep (k) [true] (R))))), .A⟩ := rfl
  have h1 : steps 0 ⟨cons true (rep (j + 1) [true, true] (cons false (L))), cons true (cons false (cons true (cons true (rep (k) [true] (R))))), .A⟩ = some ⟨rep (j + 1) [true, true] (cons true (cons false (L))), cons true (cons false (cons true (cons true (rep (k) [true] (R))))), .A⟩ := by
    simp only [steps_zero, show cons true (rep (j + 1) [true, true] (cons false (L))) = rep (j + 1) [true, true] (cons true (cons false (L))) from
      rep_rotate (j + 1) [true] [true, true] [true, true] rfl (cons false (L))]
  have c2 : ∀ L R : Tape, steps 2 ⟨app [true, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, true] R), .A⟩ := fun _ _ => rfl
  have h2 : steps ((j + 1) * 2) ⟨rep (j + 1) [true, true] (cons true (cons false (L))), cons true (cons false (cons true (cons true (rep (k) [true] (R))))), .A⟩ = some ⟨cons true (cons false (L)), cons true (rep (j + 1) [true, true] (cons false (cons true (cons true (rep (k) [true] (R)))))), .A⟩ :=
    cross_l trans c2 (j + 1) (cons true (cons false (L))) (cons false (cons true (cons true (rep (k) [true] (R)))))
  have h3 : steps 0 ⟨cons true (cons false (L)), cons true (rep (j + 1) [true, true] (cons false (cons true (cons true (rep (k) [true] (R)))))), .A⟩ = some ⟨cons true (cons false (L)), rep (j + 1) [true, true] (cons true (cons false (cons true (cons true (rep (k) [true] (R)))))), .A⟩ := by
    simp only [steps_zero, show cons true (rep (j + 1) [true, true] (cons false (cons true (cons true (rep (k) [true] (R)))))) = rep (j + 1) [true, true] (cons true (cons false (cons true (cons true (rep (k) [true] (R)))))) from
      rep_rotate (j + 1) [true] [true, true] [true, true] rfl (cons false (cons true (cons true (rep (k) [true] (R)))))]
  have c4 : ∀ L R : Tape, steps 10 ⟨app [true, false] L, app [true, true] R, .A⟩ = some ⟨app [true, false] (app [true, true] L), R, .A⟩ := fun _ _ => rfl
  have h4 : steps ((j + 1) * 10) ⟨cons true (cons false (L)), rep (j + 1) [true, true] (cons true (cons false (cons true (cons true (rep (k) [true] (R)))))), .A⟩ = some ⟨cons true (cons false (rep (j + 1) [true, true] (L))), cons true (cons false (cons true (cons true (rep (k) [true] (R))))), .A⟩ :=
    cross_r trans c4 (j + 1) (L) (cons true (cons false (cons true (cons true (rep (k) [true] (R))))))
  have h5 : steps 8 ⟨cons true (cons false (rep (j + 1) [true, true] (L))), cons true (cons false (cons true (cons true (rep (k) [true] (R))))), .A⟩ = some ⟨cons true (cons false (cons true (cons true (cons false (cons true (rep (j + 1) [true, true] (L))))))), rep (k) [true] (R), .A⟩ := rfl
  have c6 : ∀ L R : Tape, steps 5 ⟨app [true, false] L, app [true] R, .A⟩ = some ⟨app [true, false] (app [true] L), R, .A⟩ := fun _ _ => rfl
  have h6 : steps ((k) * 5) ⟨cons true (cons false (cons true (cons true (cons false (cons true (rep (j + 1) [true, true] (L))))))), rep (k) [true] (R), .A⟩ = some ⟨cons true (cons false (rep (k) [true] (cons true (cons true (cons false (cons true (rep (j + 1) [true, true] (L)))))))), R, .A⟩ :=
    cross_r trans c6 (k) (cons true (cons true (cons false (cons true (rep (j + 1) [true, true] (L)))))) (R)
  exact steps_congr trans (a := 5 + (0 + ((j + 1) * 2 + (0 + ((j + 1) * 10 + (8 + ((k) * 5))))))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (steps_seq trans h5 (h6)))))))

/-- A single 1 with an odd block of 2j+1 ones behind one 0 on its left. -/
theorem r_oneO (j : Nat) (L R : Tape) :
    steps (2 * j + 8) ⟨cons true (cons false (rep (j) [true, true] (cons true (cons false (L))))), cons false (R), .D⟩ = some ⟨L, cons false (cons true (cons true (cons true (rep (j) [true, true] (cons false (R)))))), .D⟩ := by
  have h0 : steps 5 ⟨cons true (cons false (rep (j) [true, true] (cons true (cons false (L))))), cons false (R), .D⟩ = some ⟨cons true (rep (j) [true, true] (cons true (cons false (L)))), cons true (cons false (R)), .A⟩ := rfl
  have h1 : steps 0 ⟨cons true (rep (j) [true, true] (cons true (cons false (L)))), cons true (cons false (R)), .A⟩ = some ⟨rep (j) [true, true] (cons true (cons true (cons false (L)))), cons true (cons false (R)), .A⟩ := by
    simp only [steps_zero, show cons true (rep (j) [true, true] (cons true (cons false (L)))) = rep (j) [true, true] (cons true (cons true (cons false (L)))) from
      rep_rotate (j) [true] [true, true] [true, true] rfl (cons true (cons false (L)))]
  have c2 : ∀ L R : Tape, steps 2 ⟨app [true, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, true] R), .A⟩ := fun _ _ => rfl
  have h2 : steps ((j) * 2) ⟨rep (j) [true, true] (cons true (cons true (cons false (L)))), cons true (cons false (R)), .A⟩ = some ⟨cons true (cons true (cons false (L))), cons true (rep (j) [true, true] (cons false (R))), .A⟩ :=
    cross_l trans c2 (j) (cons true (cons true (cons false (L)))) (cons false (R))
  have h3 : steps 3 ⟨cons true (cons true (cons false (L))), cons true (rep (j) [true, true] (cons false (R))), .A⟩ = some ⟨L, cons false (cons true (cons true (cons true (rep (j) [true, true] (cons false (R)))))), .D⟩ := rfl
  exact steps_congr trans (a := 5 + (0 + ((j) * 2 + (3)))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (h3))))

/-- The carrier `0 1` meets two 0s: it turns into three 1s and the head stops on the 0 before them. -/
theorem a_end (L R : Tape) :
    steps (6) ⟨cons true (cons false (L)), cons false (cons false (R)), .A⟩ = some ⟨L, cons false (cons true (cons true (cons true (R)))), .D⟩ := by
  have h0 : steps 6 ⟨cons true (cons false (L)), cons false (cons false (R)), .A⟩ = some ⟨L, cons false (cons true (cons true (cons true (R)))), .D⟩ := rfl
  exact steps_congr trans (a := 6) (by omega) (h0)

/-- The carrier `0 1` passes a block of b+2 ones that follows a single 0. -/
theorem a_pass (b : Nat) (L R : Tape) :
    steps (5 * b + 3) ⟨cons true (cons false (L)), cons false (cons true (cons true (rep (b) [true] (R)))), .A⟩ = some ⟨cons true (cons false (rep (b) [true] (cons true (cons true (cons false (L)))))), R, .A⟩ := by
  have h0 : steps 3 ⟨cons true (cons false (L)), cons false (cons true (cons true (rep (b) [true] (R)))), .A⟩ = some ⟨cons true (cons false (cons true (cons true (cons false (L))))), rep (b) [true] (R), .A⟩ := rfl
  have c1 : ∀ L R : Tape, steps 5 ⟨app [true, false] L, app [true] R, .A⟩ = some ⟨app [true, false] (app [true] L), R, .A⟩ := fun _ _ => rfl
  have h1 : steps ((b) * 5) ⟨cons true (cons false (cons true (cons true (cons false (L))))), rep (b) [true] (R), .A⟩ = some ⟨cons true (cons false (rep (b) [true] (cons true (cons true (cons false (L)))))), R, .A⟩ :=
    cross_r trans c1 (b) (cons true (cons true (cons false (L)))) (R)
  exact steps_congr trans (a := 3 + ((b) * 5)) (by omega) (steps_seq trans h0 (h1))

end H170561
