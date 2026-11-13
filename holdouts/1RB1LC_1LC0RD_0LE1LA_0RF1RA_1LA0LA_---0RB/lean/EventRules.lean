import Machine

/-! # 1RB1LC_1LC0RD_0LE1LA_0RF1RA_1LA0LA_---0RB: one round of every event

Written by `py/event_rules.py` with `bbtools.symtm` (a symbolic run, its trace checked by the kernel); every count, every tape L, R. -/

namespace H134427

open TM

/-- An odd block of 2j+3 ones left of the head: two of its 1s go, the 0 on its left becomes 1 and three 1s are written after the head (they join the block to the right). -/
theorem r_odd (j : Nat) (L R : Tape) :
    steps (12 * j + 11) ⟨rep (j + 1) [true, true] (cons true (cons false (L))), cons false (R), .C⟩ = some ⟨cons true (rep (j) [true, true] (L)), cons false (cons true (cons true (cons true (R)))), .C⟩ := by
  have h0 : steps 2 ⟨rep (j + 1) [true, true] (cons true (cons false (L))), cons false (R), .C⟩ = some ⟨rep (j) [true, true] (cons true (cons false (L))), cons true (cons false (cons false (R))), .A⟩ := rfl
  have c1 : ∀ L R : Tape, steps 2 ⟨app [true, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, true] R), .A⟩ := fun _ _ => rfl
  have h1 : steps ((j) * 2) ⟨rep (j) [true, true] (cons true (cons false (L))), cons true (cons false (cons false (R))), .A⟩ = some ⟨cons true (cons false (L)), cons true (rep (j) [true, true] (cons false (cons false (R)))), .A⟩ :=
    cross_l trans c1 (j) (cons true (cons false (L))) (cons false (cons false (R)))
  have h2 : steps 0 ⟨cons true (cons false (L)), cons true (rep (j) [true, true] (cons false (cons false (R)))), .A⟩ = some ⟨cons true (cons false (L)), rep (j) [true, true] (cons true (cons false (cons false (R)))), .A⟩ := by
    simp only [steps_zero, show cons true (rep (j) [true, true] (cons false (cons false (R)))) = rep (j) [true, true] (cons true (cons false (cons false (R)))) from
      rep_rotate (j) [true] [true, true] [true, true] rfl (cons false (cons false (R)))]
  have c3 : ∀ L R : Tape, steps 10 ⟨app [true, false] L, app [true, true] R, .A⟩ = some ⟨app [true, false] (app [true, true] L), R, .A⟩ := fun _ _ => rfl
  have h3 : steps ((j) * 10) ⟨cons true (cons false (L)), rep (j) [true, true] (cons true (cons false (cons false (R)))), .A⟩ = some ⟨cons true (cons false (rep (j) [true, true] (L))), cons true (cons false (cons false (R))), .A⟩ :=
    cross_r trans c3 (j) (L) (cons true (cons false (cons false (R))))
  have h4 : steps 9 ⟨cons true (cons false (rep (j) [true, true] (L))), cons true (cons false (cons false (R))), .A⟩ = some ⟨cons true (rep (j) [true, true] (L)), cons false (cons true (cons true (cons true (R)))), .C⟩ := rfl
  exact steps_congr trans (a := 2 + ((j) * 2 + (0 + ((j) * 10 + (9))))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

/-- An even block of 2j+2 ones left of the head: the head erases its last 1 and comes to rest on the 0 on its left. -/
theorem r_shift (j : Nat) (L R : Tape) :
    steps (2 * j + 3) ⟨rep (j + 1) [true, true] (cons false (L)), cons false (R), .C⟩ = some ⟨L, cons false (cons true (rep (j) [true, true] (cons false (cons false (R))))), .C⟩ := by
  have h0 : steps 2 ⟨rep (j + 1) [true, true] (cons false (L)), cons false (R), .C⟩ = some ⟨rep (j) [true, true] (cons false (L)), cons true (cons false (cons false (R))), .A⟩ := rfl
  have c1 : ∀ L R : Tape, steps 2 ⟨app [true, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, true] R), .A⟩ := fun _ _ => rfl
  have h1 : steps ((j) * 2) ⟨rep (j) [true, true] (cons false (L)), cons true (cons false (cons false (R))), .A⟩ = some ⟨cons false (L), cons true (rep (j) [true, true] (cons false (cons false (R)))), .A⟩ :=
    cross_l trans c1 (j) (cons false (L)) (cons false (cons false (R)))
  have h2 : steps 1 ⟨cons false (L), cons true (rep (j) [true, true] (cons false (cons false (R)))), .A⟩ = some ⟨L, cons false (cons true (rep (j) [true, true] (cons false (cons false (R))))), .C⟩ := rfl
  exact steps_congr trans (a := 2 + ((j) * 2 + (1))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (h2)))

/-- An even block of 2j+4 ones with three 0s on its left: one 1 is written before the three 0s, the block loses four 1s and three 1s are written after the head. -/
theorem r_split (j : Nat) (L R : Tape) :
    steps (12 * j + 17) ⟨rep (j + 2) [true, true] (cons false (cons false (cons false (L)))), cons false (R), .C⟩ = some ⟨rep (j) [true, true] (cons false (cons false (cons false (cons true (L))))), cons false (cons true (cons true (cons true (R)))), .C⟩ := by
  have h0 : steps 2 ⟨rep (j + 2) [true, true] (cons false (cons false (cons false (L)))), cons false (R), .C⟩ = some ⟨rep (j + 1) [true, true] (cons false (cons false (cons false (L)))), cons true (cons false (cons false (R))), .A⟩ := rfl
  have c1 : ∀ L R : Tape, steps 2 ⟨app [true, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, true] R), .A⟩ := fun _ _ => rfl
  have h1 : steps ((j + 1) * 2) ⟨rep (j + 1) [true, true] (cons false (cons false (cons false (L)))), cons true (cons false (cons false (R))), .A⟩ = some ⟨cons false (cons false (cons false (L))), cons true (rep (j + 1) [true, true] (cons false (cons false (R)))), .A⟩ :=
    cross_l trans c1 (j + 1) (cons false (cons false (cons false (L)))) (cons false (cons false (R)))
  have h2 : steps 9 ⟨cons false (cons false (cons false (L))), cons true (rep (j + 1) [true, true] (cons false (cons false (R)))), .A⟩ = some ⟨cons true (cons false (cons false (cons false (cons false (cons true (L)))))), rep (j) [true, true] (cons false (cons false (R))), .A⟩ := rfl
  have c3 : ∀ L R : Tape, steps 10 ⟨app [true, false] L, app [true, true] R, .A⟩ = some ⟨app [true, false] (app [true, true] L), R, .A⟩ := fun _ _ => rfl
  have h3 : steps ((j) * 10) ⟨cons true (cons false (cons false (cons false (cons false (cons true (L)))))), rep (j) [true, true] (cons false (cons false (R))), .A⟩ = some ⟨cons true (cons false (rep (j) [true, true] (cons false (cons false (cons false (cons true (L))))))), cons false (cons false (R)), .A⟩ :=
    cross_r trans c3 (j) (cons false (cons false (cons false (cons true (L))))) (cons false (cons false (R)))
  have h4 : steps 4 ⟨cons true (cons false (rep (j) [true, true] (cons false (cons false (cons false (cons true (L))))))), cons false (cons false (R)), .A⟩ = some ⟨rep (j) [true, true] (cons false (cons false (cons false (cons true (L))))), cons false (cons true (cons true (cons true (R)))), .C⟩ := rfl
  exact steps_congr trans (a := 2 + ((j + 1) * 2 + (9 + ((j) * 10 + (4))))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

/-- A block of exactly two 1s with three 0s on its left: it moves three cells left and one 1 is written after the head. -/
theorem r_two (L R : Tape) :
    steps (17) ⟨cons true (cons true (cons false (cons false (cons false (L))))), cons false (R), .C⟩ = some ⟨cons false (cons false (cons true (cons true (L)))), cons false (cons true (R)), .C⟩ := by
  have h0 : steps 17 ⟨cons true (cons true (cons false (cons false (cons false (L))))), cons false (R), .C⟩ = some ⟨cons false (cons false (cons true (cons true (L)))), cons false (cons true (R)), .C⟩ := rfl
  exact steps_congr trans (a := 17) (by omega) (h0)

/-- No block left of the head (two 0s): the block of k+3 ones on the right gives one 1 to the left, moves left and the head ends right of it behind a carrier `0 1`. -/
theorem r_zero (k : Nat) (L R : Tape) :
    steps (5 * k + 8) ⟨cons false (cons false (L)), cons false (cons true (cons true (cons true (rep (k) [true] (R))))), .C⟩ = some ⟨cons true (cons false (rep (k) [true] (cons false (cons false (cons false (cons true (L))))))), R, .A⟩ := by
  have h0 : steps 8 ⟨cons false (cons false (L)), cons false (cons true (cons true (cons true (rep (k) [true] (R))))), .C⟩ = some ⟨cons true (cons false (cons false (cons false (cons false (cons true (L)))))), rep (k) [true] (R), .A⟩ := rfl
  have c1 : ∀ L R : Tape, steps 5 ⟨app [true, false] L, app [true] R, .A⟩ = some ⟨app [true, false] (app [true] L), R, .A⟩ := fun _ _ => rfl
  have h1 : steps ((k) * 5) ⟨cons true (cons false (cons false (cons false (cons false (cons true (L)))))), rep (k) [true] (R), .A⟩ = some ⟨cons true (cons false (rep (k) [true] (cons false (cons false (cons false (cons true (L))))))), R, .A⟩ :=
    cross_r trans c1 (k) (cons false (cons false (cons false (cons true (L))))) (R)
  exact steps_congr trans (a := 8 + ((k) * 5)) (by omega) (steps_seq trans h0 (h1))

/-- One 0 left of the head and then an even block of 2j+2 ones: the block moves one cell left and the head crosses the block on the right. -/
theorem r_zeroE (j k : Nat) (L R : Tape) :
    steps (12 * j + 5 * k + 15) ⟨cons false (rep (j + 1) [true, true] (cons false (L))), cons false (cons true (cons true (rep (k) [true] (R)))), .C⟩ = some ⟨cons true (cons false (rep (k) [true] (cons true (cons true (cons false (cons true (cons true (rep (j) [true, true] (L))))))))), R, .A⟩ := by
  have h0 : steps 2 ⟨cons false (rep (j + 1) [true, true] (cons false (L))), cons false (cons true (cons true (rep (k) [true] (R)))), .C⟩ = some ⟨cons true (rep (j) [true, true] (cons false (L))), cons true (cons true (cons false (cons true (cons true (rep (k) [true] (R)))))), .A⟩ := rfl
  have h1 : steps 0 ⟨cons true (rep (j) [true, true] (cons false (L))), cons true (cons true (cons false (cons true (cons true (rep (k) [true] (R)))))), .A⟩ = some ⟨rep (j) [true, true] (cons true (cons false (L))), cons true (cons true (cons false (cons true (cons true (rep (k) [true] (R)))))), .A⟩ := by
    simp only [steps_zero, show cons true (rep (j) [true, true] (cons false (L))) = rep (j) [true, true] (cons true (cons false (L))) from
      rep_rotate (j) [true] [true, true] [true, true] rfl (cons false (L))]
  have c2 : ∀ L R : Tape, steps 2 ⟨app [true, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, true] R), .A⟩ := fun _ _ => rfl
  have h2 : steps ((j) * 2) ⟨rep (j) [true, true] (cons true (cons false (L))), cons true (cons true (cons false (cons true (cons true (rep (k) [true] (R)))))), .A⟩ = some ⟨cons true (cons false (L)), cons true (rep (j) [true, true] (cons true (cons false (cons true (cons true (rep (k) [true] (R))))))), .A⟩ :=
    cross_l trans c2 (j) (cons true (cons false (L))) (cons true (cons false (cons true (cons true (rep (k) [true] (R))))))
  have h3 : steps 0 ⟨cons true (cons false (L)), cons true (rep (j) [true, true] (cons true (cons false (cons true (cons true (rep (k) [true] (R))))))), .A⟩ = some ⟨cons true (cons false (L)), rep (j) [true, true] (cons true (cons true (cons false (cons true (cons true (rep (k) [true] (R))))))), .A⟩ := by
    simp only [steps_zero, show cons true (rep (j) [true, true] (cons true (cons false (cons true (cons true (rep (k) [true] (R))))))) = rep (j) [true, true] (cons true (cons true (cons false (cons true (cons true (rep (k) [true] (R))))))) from
      rep_rotate (j) [true] [true, true] [true, true] rfl (cons true (cons false (cons true (cons true (rep (k) [true] (R))))))]
  have c4 : ∀ L R : Tape, steps 10 ⟨app [true, false] L, app [true, true] R, .A⟩ = some ⟨app [true, false] (app [true, true] L), R, .A⟩ := fun _ _ => rfl
  have h4 : steps ((j) * 10) ⟨cons true (cons false (L)), rep (j) [true, true] (cons true (cons true (cons false (cons true (cons true (rep (k) [true] (R))))))), .A⟩ = some ⟨cons true (cons false (rep (j) [true, true] (L))), cons true (cons true (cons false (cons true (cons true (rep (k) [true] (R)))))), .A⟩ :=
    cross_r trans c4 (j) (L) (cons true (cons true (cons false (cons true (cons true (rep (k) [true] (R)))))))
  have h5 : steps 13 ⟨cons true (cons false (rep (j) [true, true] (L))), cons true (cons true (cons false (cons true (cons true (rep (k) [true] (R)))))), .A⟩ = some ⟨cons true (cons false (cons true (cons true (cons false (cons true (cons true (rep (j) [true, true] (L)))))))), rep (k) [true] (R), .A⟩ := rfl
  have c6 : ∀ L R : Tape, steps 5 ⟨app [true, false] L, app [true] R, .A⟩ = some ⟨app [true, false] (app [true] L), R, .A⟩ := fun _ _ => rfl
  have h6 : steps ((k) * 5) ⟨cons true (cons false (cons true (cons true (cons false (cons true (cons true (rep (j) [true, true] (L)))))))), rep (k) [true] (R), .A⟩ = some ⟨cons true (cons false (rep (k) [true] (cons true (cons true (cons false (cons true (cons true (rep (j) [true, true] (L))))))))), R, .A⟩ :=
    cross_r trans c6 (k) (cons true (cons true (cons false (cons true (cons true (rep (j) [true, true] (L))))))) (R)
  exact steps_congr trans (a := 2 + (0 + ((j) * 2 + (0 + ((j) * 10 + (13 + ((k) * 5))))))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (steps_seq trans h5 (h6)))))))

/-- One 0 left of the head and then an odd block of 2j+1 ones: the block gains a 1 and the head comes to rest on the 0 on its left. -/
theorem r_zeroO (j : Nat) (L R : Tape) :
    steps (2 * j + 3) ⟨cons false (cons true (rep (j) [true, true] (cons false (L)))), cons false (R), .C⟩ = some ⟨L, cons false (cons true (rep (j) [true, true] (cons true (cons false (R))))), .C⟩ := by
  have h0 : steps 2 ⟨cons false (cons true (rep (j) [true, true] (cons false (L)))), cons false (R), .C⟩ = some ⟨rep (j) [true, true] (cons false (L)), cons true (cons true (cons false (R))), .A⟩ := rfl
  have c1 : ∀ L R : Tape, steps 2 ⟨app [true, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, true] R), .A⟩ := fun _ _ => rfl
  have h1 : steps ((j) * 2) ⟨rep (j) [true, true] (cons false (L)), cons true (cons true (cons false (R))), .A⟩ = some ⟨cons false (L), cons true (rep (j) [true, true] (cons true (cons false (R)))), .A⟩ :=
    cross_l trans c1 (j) (cons false (L)) (cons true (cons false (R)))
  have h2 : steps 1 ⟨cons false (L), cons true (rep (j) [true, true] (cons true (cons false (R)))), .A⟩ = some ⟨L, cons false (cons true (rep (j) [true, true] (cons true (cons false (R))))), .C⟩ := rfl
  exact steps_congr trans (a := 2 + ((j) * 2 + (1))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (h2)))

/-- A single 1 with two 0s on its left. -/
theorem r_one (k : Nat) (L R : Tape) :
    steps (5 * k + 11) ⟨cons true (cons false (cons false (L))), cons false (cons true (cons true (rep (k) [true] (R)))), .C⟩ = some ⟨cons true (cons false (rep (k) [true] (cons true (cons true (cons false (cons true (L))))))), R, .A⟩ := by
  have h0 : steps 11 ⟨cons true (cons false (cons false (L))), cons false (cons true (cons true (rep (k) [true] (R)))), .C⟩ = some ⟨cons true (cons false (cons true (cons true (cons false (cons true (L)))))), rep (k) [true] (R), .A⟩ := rfl
  have c1 : ∀ L R : Tape, steps 5 ⟨app [true, false] L, app [true] R, .A⟩ = some ⟨app [true, false] (app [true] L), R, .A⟩ := fun _ _ => rfl
  have h1 : steps ((k) * 5) ⟨cons true (cons false (cons true (cons true (cons false (cons true (L)))))), rep (k) [true] (R), .A⟩ = some ⟨cons true (cons false (rep (k) [true] (cons true (cons true (cons false (cons true (L))))))), R, .A⟩ :=
    cross_r trans c1 (k) (cons true (cons true (cons false (cons true (L))))) (R)
  exact steps_congr trans (a := 11 + ((k) * 5)) (by omega) (steps_seq trans h0 (h1))

/-- A single 1 with an even block of 2j+2 ones behind one 0 on its left. -/
theorem r_oneE (j k : Nat) (L R : Tape) :
    steps (12 * j + 5 * k + 23) ⟨cons true (cons false (rep (j + 1) [true, true] (cons false (L)))), cons false (cons true (cons true (rep (k) [true] (R)))), .C⟩ = some ⟨cons true (cons false (rep (k) [true] (cons true (cons true (cons false (cons true (cons true (rep (j) [true, true] (cons true (L)))))))))), R, .A⟩ := by
  have h0 : steps 4 ⟨cons true (cons false (rep (j + 1) [true, true] (cons false (L)))), cons false (cons true (cons true (rep (k) [true] (R)))), .C⟩ = some ⟨rep (j + 1) [true, true] (cons false (L)), cons true (cons true (cons false (cons true (cons true (rep (k) [true] (R)))))), .C⟩ := rfl
  have c1 : ∀ L R : Tape, steps 2 ⟨app [true, true] L, app [true] R, .C⟩ = some ⟨L, app [true] (app [true, true] R), .C⟩ := fun _ _ => rfl
  have h1 : steps ((j + 1) * 2) ⟨rep (j + 1) [true, true] (cons false (L)), cons true (cons true (cons false (cons true (cons true (rep (k) [true] (R)))))), .C⟩ = some ⟨cons false (L), cons true (rep (j + 1) [true, true] (cons true (cons false (cons true (cons true (rep (k) [true] (R))))))), .C⟩ :=
    cross_l trans c1 (j + 1) (cons false (L)) (cons true (cons false (cons true (cons true (rep (k) [true] (R))))))
  have h2 : steps 4 ⟨cons false (L), cons true (rep (j + 1) [true, true] (cons true (cons false (cons true (cons true (rep (k) [true] (R))))))), .C⟩ = some ⟨cons true (cons false (cons true (L))), cons true (rep (j) [true, true] (cons true (cons false (cons true (cons true (rep (k) [true] (R))))))), .A⟩ := rfl
  have h3 : steps 0 ⟨cons true (cons false (cons true (L))), cons true (rep (j) [true, true] (cons true (cons false (cons true (cons true (rep (k) [true] (R))))))), .A⟩ = some ⟨cons true (cons false (cons true (L))), rep (j) [true, true] (cons true (cons true (cons false (cons true (cons true (rep (k) [true] (R))))))), .A⟩ := by
    simp only [steps_zero, show cons true (rep (j) [true, true] (cons true (cons false (cons true (cons true (rep (k) [true] (R))))))) = rep (j) [true, true] (cons true (cons true (cons false (cons true (cons true (rep (k) [true] (R))))))) from
      rep_rotate (j) [true] [true, true] [true, true] rfl (cons true (cons false (cons true (cons true (rep (k) [true] (R))))))]
  have c4 : ∀ L R : Tape, steps 10 ⟨app [true, false] L, app [true, true] R, .A⟩ = some ⟨app [true, false] (app [true, true] L), R, .A⟩ := fun _ _ => rfl
  have h4 : steps ((j) * 10) ⟨cons true (cons false (cons true (L))), rep (j) [true, true] (cons true (cons true (cons false (cons true (cons true (rep (k) [true] (R))))))), .A⟩ = some ⟨cons true (cons false (rep (j) [true, true] (cons true (L)))), cons true (cons true (cons false (cons true (cons true (rep (k) [true] (R)))))), .A⟩ :=
    cross_r trans c4 (j) (cons true (L)) (cons true (cons true (cons false (cons true (cons true (rep (k) [true] (R)))))))
  have h5 : steps 13 ⟨cons true (cons false (rep (j) [true, true] (cons true (L)))), cons true (cons true (cons false (cons true (cons true (rep (k) [true] (R)))))), .A⟩ = some ⟨cons true (cons false (cons true (cons true (cons false (cons true (cons true (rep (j) [true, true] (cons true (L))))))))), rep (k) [true] (R), .A⟩ := rfl
  have c6 : ∀ L R : Tape, steps 5 ⟨app [true, false] L, app [true] R, .A⟩ = some ⟨app [true, false] (app [true] L), R, .A⟩ := fun _ _ => rfl
  have h6 : steps ((k) * 5) ⟨cons true (cons false (cons true (cons true (cons false (cons true (cons true (rep (j) [true, true] (cons true (L))))))))), rep (k) [true] (R), .A⟩ = some ⟨cons true (cons false (rep (k) [true] (cons true (cons true (cons false (cons true (cons true (rep (j) [true, true] (cons true (L)))))))))), R, .A⟩ :=
    cross_r trans c6 (k) (cons true (cons true (cons false (cons true (cons true (rep (j) [true, true] (cons true (L)))))))) (R)
  exact steps_congr trans (a := 4 + ((j + 1) * 2 + (4 + (0 + ((j) * 10 + (13 + ((k) * 5))))))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (steps_seq trans h5 (h6)))))))

/-- A single 1 with an odd block of 2j+1 ones behind one 0 on its left. -/
theorem r_oneO (j : Nat) (L R : Tape) :
    steps (2 * j + 6) ⟨cons true (cons false (rep (j) [true, true] (cons true (cons false (L))))), cons false (R), .C⟩ = some ⟨L, cons false (cons true (cons true (rep (j) [true, true] (cons true (cons false (R)))))), .C⟩ := by
  have h0 : steps 4 ⟨cons true (cons false (rep (j) [true, true] (cons true (cons false (L))))), cons false (R), .C⟩ = some ⟨rep (j) [true, true] (cons true (cons false (L))), cons true (cons true (cons false (R))), .C⟩ := rfl
  have c1 : ∀ L R : Tape, steps 2 ⟨app [true, true] L, app [true] R, .C⟩ = some ⟨L, app [true] (app [true, true] R), .C⟩ := fun _ _ => rfl
  have h1 : steps ((j) * 2) ⟨rep (j) [true, true] (cons true (cons false (L))), cons true (cons true (cons false (R))), .C⟩ = some ⟨cons true (cons false (L)), cons true (rep (j) [true, true] (cons true (cons false (R)))), .C⟩ :=
    cross_l trans c1 (j) (cons true (cons false (L))) (cons true (cons false (R)))
  have h2 : steps 2 ⟨cons true (cons false (L)), cons true (rep (j) [true, true] (cons true (cons false (R)))), .C⟩ = some ⟨L, cons false (cons true (cons true (rep (j) [true, true] (cons true (cons false (R)))))), .C⟩ := rfl
  exact steps_congr trans (a := 4 + ((j) * 2 + (2))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (h2)))

/-- The carrier `0 1` meets two 0s: it turns into three 1s and the head stops on the 0 before them. -/
theorem a_end (L R : Tape) :
    steps (4) ⟨cons true (cons false (L)), cons false (cons false (R)), .A⟩ = some ⟨L, cons false (cons true (cons true (cons true (R)))), .C⟩ := by
  have h0 : steps 4 ⟨cons true (cons false (L)), cons false (cons false (R)), .A⟩ = some ⟨L, cons false (cons true (cons true (cons true (R)))), .C⟩ := rfl
  exact steps_congr trans (a := 4) (by omega) (h0)

/-- The carrier `0 1` passes a block of b+2 ones that follows a single 0. -/
theorem a_pass (b : Nat) (L R : Tape) :
    steps (5 * b + 3) ⟨cons true (cons false (L)), cons false (cons true (cons true (rep (b) [true] (R)))), .A⟩ = some ⟨cons true (cons false (rep (b) [true] (cons true (cons true (cons false (L)))))), R, .A⟩ := by
  have h0 : steps 3 ⟨cons true (cons false (L)), cons false (cons true (cons true (rep (b) [true] (R)))), .A⟩ = some ⟨cons true (cons false (cons true (cons true (cons false (L))))), rep (b) [true] (R), .A⟩ := rfl
  have c1 : ∀ L R : Tape, steps 5 ⟨app [true, false] L, app [true] R, .A⟩ = some ⟨app [true, false] (app [true] L), R, .A⟩ := fun _ _ => rfl
  have h1 : steps ((b) * 5) ⟨cons true (cons false (cons true (cons true (cons false (L))))), rep (b) [true] (R), .A⟩ = some ⟨cons true (cons false (rep (b) [true] (cons true (cons true (cons false (L)))))), R, .A⟩ :=
    cross_r trans c1 (b) (cons true (cons true (cons false (L)))) (R)
  exact steps_congr trans (a := 3 + ((b) * 5)) (by omega) (steps_seq trans h0 (h1))

end H134427
