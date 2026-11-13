import Machine

/-! # 1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE: the cell rules

Written by `py/gen_rules.py` (`bbtools.symtm.prove`); every theorem is a chain of `rfl` steps and shift rules. -/

namespace H15252

open TM

/-- F walks left over a unit `1 0`, which reappears on its right -/
theorem walk (j : Nat) (L R : Tape) :
    steps (2 * j) ⟨rep (j) [true, false] (L), cons false (cons false (R)), .F⟩ = some ⟨L, cons false (rep (j) [false, true] (cons false (R))), .F⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .F⟩ = some ⟨L, app [false] (app [false, true] R), .F⟩ := fun _ _ => rfl
  have h0 : steps ((j) * 2) ⟨rep (j) [true, false] (L), cons false (cons false (R)), .F⟩ = some ⟨L, cons false (rep (j) [false, true] (cons false (R))), .F⟩ :=
    cross_l trans c0 (j) (L) (cons false (R))
  exact steps_congr trans (a := (j) * 2) (by omega) (h0)

/-- one round at a block of at least three: two 1s off each side, two new units -/
theorem round (Y k : Nat) (L R : Tape) :
    steps (4 * k + 14) ⟨rep (3) [true] (L), cons false (cons false (rep (k) [true, false] (rep (2) [true] (rep (Y) [true] (R))))), .F⟩ = some ⟨cons true (rep (k) [false, true] (cons false (cons true (cons false (cons true (L)))))), cons false (cons false (rep (Y) [true] (R))), .F⟩ := by
  have h0 : steps 9 ⟨rep (3) [true] (L), cons false (cons false (rep (k) [true, false] (rep (2) [true] (rep (Y) [true] (R))))), .F⟩ = some ⟨cons false (cons true (cons false (cons true (L)))), cons false (rep (k) [true, false] (rep (2) [true] (rep (Y) [true] (R)))), .A⟩ := rfl
  have h1 : steps 0 ⟨cons false (cons true (cons false (cons true (L)))), cons false (rep (k) [true, false] (rep (2) [true] (rep (Y) [true] (R)))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (L)))), rep (k) [false, true] (cons false (rep (2) [true] (rep (Y) [true] (R)))), .A⟩ := by
    simp only [steps_zero, show cons false (rep (k) [true, false] (rep (2) [true] (rep (Y) [true] (R)))) = rep (k) [false, true] (cons false (rep (2) [true] (rep (Y) [true] (R)))) from
      rep_rotate (k) [false] [true, false] [false, true] rfl (rep (2) [true] (rep (Y) [true] (R)))]
  have c2 : ∀ L R : Tape, steps 4 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [false, true] L), R, .A⟩ := fun _ _ => rfl
  have h2 : steps ((k) * 4) ⟨cons false (cons true (cons false (cons true (L)))), rep (k) [false, true] (cons false (rep (2) [true] (rep (Y) [true] (R)))), .A⟩ = some ⟨rep (k) [false, true] (cons false (cons true (cons false (cons true (L))))), cons false (rep (2) [true] (rep (Y) [true] (R))), .A⟩ :=
    cross_r trans c2 (k) (cons false (cons true (cons false (cons true (L))))) (cons false (rep (2) [true] (rep (Y) [true] (R))))
  have h3 : steps 5 ⟨rep (k) [false, true] (cons false (cons true (cons false (cons true (L))))), cons false (rep (2) [true] (rep (Y) [true] (R))), .A⟩ = some ⟨cons true (rep (k) [false, true] (cons false (cons true (cons false (cons true (L)))))), cons false (cons false (rep (Y) [true] (R))), .F⟩ := rfl
  exact steps_congr trans (a := 9 + (0 + ((k) * 4 + (5)))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (h3))))

/-- the same round with nothing left of the head -/
theorem roundz (Y k : Nat) (R : Tape) :
    steps (4 * k + 10) ⟨blank, cons false (cons false (rep (k) [true, false] (rep (2) [true] (rep (Y) [true] (R))))), .F⟩ = some ⟨cons true (rep (k) [false, true] (cons false (cons true (blank)))), cons false (cons false (rep (Y) [true] (R))), .F⟩ := by
  have h0 : steps 5 ⟨blank, cons false (cons false (rep (k) [true, false] (rep (2) [true] (rep (Y) [true] (R))))), .F⟩ = some ⟨cons false (cons true (blank)), cons false (rep (k) [true, false] (rep (2) [true] (rep (Y) [true] (R)))), .A⟩ := rfl
  have h1 : steps 0 ⟨cons false (cons true (blank)), cons false (rep (k) [true, false] (rep (2) [true] (rep (Y) [true] (R)))), .A⟩ = some ⟨cons false (cons true (blank)), rep (k) [false, true] (cons false (rep (2) [true] (rep (Y) [true] (R)))), .A⟩ := by
    simp only [steps_zero, show cons false (rep (k) [true, false] (rep (2) [true] (rep (Y) [true] (R)))) = rep (k) [false, true] (cons false (rep (2) [true] (rep (Y) [true] (R)))) from
      rep_rotate (k) [false] [true, false] [false, true] rfl (rep (2) [true] (rep (Y) [true] (R)))]
  have c2 : ∀ L R : Tape, steps 4 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [false, true] L), R, .A⟩ := fun _ _ => rfl
  have h2 : steps ((k) * 4) ⟨cons false (cons true (blank)), rep (k) [false, true] (cons false (rep (2) [true] (rep (Y) [true] (R)))), .A⟩ = some ⟨rep (k) [false, true] (cons false (cons true (blank))), cons false (rep (2) [true] (rep (Y) [true] (R))), .A⟩ :=
    cross_r trans c2 (k) (cons false (cons true (blank))) (cons false (rep (2) [true] (rep (Y) [true] (R))))
  have h3 : steps 5 ⟨rep (k) [false, true] (cons false (cons true (blank))), cons false (rep (2) [true] (rep (Y) [true] (R))), .A⟩ = some ⟨cons true (rep (k) [false, true] (cons false (cons true (blank)))), cons false (cons false (rep (Y) [true] (R))), .F⟩ := rfl
  exact steps_congr trans (a := 5 + (0 + ((k) * 4 + (5)))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (h3))))

/-- a gap of two 0s: the units and the next block merge into one block, four 1s off the left block -/
theorem merge (Z k : Nat) (L R : Tape) :
    steps (6 * k + 20) ⟨rep (5) [true] (L), cons false (cons false (rep (k) [true, false] (cons false (rep (Z) [true] (cons false (R)))))), .F⟩ = some ⟨cons true (L), cons false (cons false (cons true (cons true (cons true (cons true (cons true (rep (k) [true, true] (rep (Z) [true] (cons false (R)))))))))), .F⟩ := by
  have h0 : steps 9 ⟨rep (5) [true] (L), cons false (cons false (rep (k) [true, false] (cons false (rep (Z) [true] (cons false (R)))))), .F⟩ = some ⟨cons false (cons true (cons false (cons true (rep (2) [true] (L))))), cons false (rep (k) [true, false] (cons false (rep (Z) [true] (cons false (R))))), .A⟩ := rfl
  have h1 : steps 0 ⟨cons false (cons true (cons false (cons true (rep (2) [true] (L))))), cons false (rep (k) [true, false] (cons false (rep (Z) [true] (cons false (R))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (rep (2) [true] (L))))), rep (k) [false, true] (cons false (cons false (rep (Z) [true] (cons false (R))))), .A⟩ := by
    simp only [steps_zero, show cons false (rep (k) [true, false] (cons false (rep (Z) [true] (cons false (R))))) = rep (k) [false, true] (cons false (cons false (rep (Z) [true] (cons false (R))))) from
      rep_rotate (k) [false] [true, false] [false, true] rfl (cons false (rep (Z) [true] (cons false (R))))]
  have c2 : ∀ L R : Tape, steps 4 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [false, true] L), R, .A⟩ := fun _ _ => rfl
  have h2 : steps ((k) * 4) ⟨cons false (cons true (cons false (cons true (rep (2) [true] (L))))), rep (k) [false, true] (cons false (cons false (rep (Z) [true] (cons false (R))))), .A⟩ = some ⟨rep (k) [false, true] (cons false (cons true (cons false (cons true (rep (2) [true] (L)))))), cons false (cons false (rep (Z) [true] (cons false (R)))), .A⟩ :=
    cross_r trans c2 (k) (cons false (cons true (cons false (cons true (rep (2) [true] (L)))))) (cons false (cons false (rep (Z) [true] (cons false (R)))))
  have h3 : steps 1 ⟨rep (k) [false, true] (cons false (cons true (cons false (cons true (rep (2) [true] (L)))))), cons false (cons false (rep (Z) [true] (cons false (R)))), .A⟩ = some ⟨cons true (rep (k) [false, true] (cons false (cons true (cons false (cons true (rep (2) [true] (L))))))), cons false (rep (Z) [true] (cons false (R))), .B⟩ := rfl
  have h4 : steps 0 ⟨cons true (rep (k) [false, true] (cons false (cons true (cons false (cons true (rep (2) [true] (L))))))), cons false (rep (Z) [true] (cons false (R))), .B⟩ = some ⟨rep (k) [true, false] (cons true (cons false (cons true (cons false (cons true (rep (2) [true] (L))))))), cons false (rep (Z) [true] (cons false (R))), .B⟩ := by
    simp only [steps_zero, show cons true (rep (k) [false, true] (cons false (cons true (cons false (cons true (rep (2) [true] (L))))))) = rep (k) [true, false] (cons true (cons false (cons true (cons false (cons true (rep (2) [true] (L))))))) from
      rep_rotate (k) [true] [false, true] [true, false] rfl (cons false (cons true (cons false (cons true (rep (2) [true] (L))))))]
  have c5 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .B⟩ = some ⟨L, app [false] (app [true, true] R), .B⟩ := fun _ _ => rfl
  have h5 : steps ((k) * 2) ⟨rep (k) [true, false] (cons true (cons false (cons true (cons false (cons true (rep (2) [true] (L))))))), cons false (rep (Z) [true] (cons false (R))), .B⟩ = some ⟨cons true (cons false (cons true (cons false (cons true (rep (2) [true] (L)))))), cons false (rep (k) [true, true] (rep (Z) [true] (cons false (R)))), .B⟩ :=
    cross_l trans c5 (k) (cons true (cons false (cons true (cons false (cons true (rep (2) [true] (L))))))) (rep (Z) [true] (cons false (R)))
  have h6 : steps 10 ⟨cons true (cons false (cons true (cons false (cons true (rep (2) [true] (L)))))), cons false (rep (k) [true, true] (rep (Z) [true] (cons false (R)))), .B⟩ = some ⟨cons true (L), cons false (cons false (cons true (cons true (cons true (cons true (cons true (rep (k) [true, true] (rep (Z) [true] (cons false (R)))))))))), .F⟩ := rfl
  exact steps_congr trans (a := 9 + (0 + ((k) * 4 + (1 + (0 + ((k) * 2 + (10))))))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (steps_seq trans h5 (h6)))))))

/-- nothing left of the head and a gap: everything merges into a new left block -/
theorem restart (W Z k : Nat) (R : Tape) :
    steps (Z + 8 * k + 19) ⟨blank, cons false (cons false (rep (k) [true, false] (cons false (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))))))), .F⟩ = some ⟨rep (Z) [true] (cons true (rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (blank)))))))), cons false (cons false (rep (W) [true] (cons false (R)))), .F⟩ := by
  have h0 : steps 5 ⟨blank, cons false (cons false (rep (k) [true, false] (cons false (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))))))), .F⟩ = some ⟨cons false (cons true (blank)), cons false (rep (k) [true, false] (cons false (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R)))))))), .A⟩ := rfl
  have h1 : steps 0 ⟨cons false (cons true (blank)), cons false (rep (k) [true, false] (cons false (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R)))))))), .A⟩ = some ⟨cons false (cons true (blank)), rep (k) [false, true] (cons false (cons false (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R)))))))), .A⟩ := by
    simp only [steps_zero, show cons false (rep (k) [true, false] (cons false (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R)))))))) = rep (k) [false, true] (cons false (cons false (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R)))))))) from
      rep_rotate (k) [false] [true, false] [false, true] rfl (cons false (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R)))))))]
  have c2 : ∀ L R : Tape, steps 4 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [false, true] L), R, .A⟩ := fun _ _ => rfl
  have h2 : steps ((k) * 4) ⟨cons false (cons true (blank)), rep (k) [false, true] (cons false (cons false (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R)))))))), .A⟩ = some ⟨rep (k) [false, true] (cons false (cons true (blank))), cons false (cons false (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))))), .A⟩ :=
    cross_r trans c2 (k) (cons false (cons true (blank))) (cons false (cons false (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))))))
  have h3 : steps 1 ⟨rep (k) [false, true] (cons false (cons true (blank))), cons false (cons false (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))))), .A⟩ = some ⟨cons true (rep (k) [false, true] (cons false (cons true (blank)))), cons false (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R)))))), .B⟩ := rfl
  have h4 : steps 0 ⟨cons true (rep (k) [false, true] (cons false (cons true (blank)))), cons false (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R)))))), .B⟩ = some ⟨rep (k) [true, false] (cons true (cons false (cons true (blank)))), cons false (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R)))))), .B⟩ := by
    simp only [steps_zero, show cons true (rep (k) [false, true] (cons false (cons true (blank)))) = rep (k) [true, false] (cons true (cons false (cons true (blank)))) from
      rep_rotate (k) [true] [false, true] [true, false] rfl (cons false (cons true (blank)))]
  have c5 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .B⟩ = some ⟨L, app [false] (app [true, true] R), .B⟩ := fun _ _ => rfl
  have h5 : steps ((k) * 2) ⟨rep (k) [true, false] (cons true (cons false (cons true (blank)))), cons false (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R)))))), .B⟩ = some ⟨cons true (cons false (cons true (blank))), cons false (rep (k) [true, true] (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))))), .B⟩ :=
    cross_l trans c5 (k) (cons true (cons false (cons true (blank)))) (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))))
  have h6 : steps 10 ⟨cons true (cons false (cons true (blank))), cons false (rep (k) [true, true] (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))))), .B⟩ = some ⟨cons true (cons true (cons true (cons true (cons true (blank))))), cons true (rep (k) [true, true] (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))))), .E⟩ := rfl
  have h7 : steps 0 ⟨cons true (cons true (cons true (cons true (cons true (blank))))), cons true (rep (k) [true, true] (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))))), .E⟩ = some ⟨cons true (cons true (cons true (cons true (cons true (blank))))), rep (k) [true, true] (cons true (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))))), .E⟩ := by
    simp only [steps_zero, show cons true (rep (k) [true, true] (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))))) = rep (k) [true, true] (cons true (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))))) from
      rep_rotate (k) [true] [true, true] [true, true] rfl (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))))]
  have c8 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, true] R, .E⟩ = some ⟨app [] (app [true, true] L), R, .E⟩ := fun _ _ => rfl
  have h8 : steps ((k) * 2) ⟨cons true (cons true (cons true (cons true (cons true (blank))))), rep (k) [true, true] (cons true (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))))), .E⟩ = some ⟨rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (blank)))))), cons true (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R)))))), .E⟩ :=
    cross_r trans c8 (k) (cons true (cons true (cons true (cons true (cons true (blank)))))) (cons true (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R)))))))
  have h9 : steps 1 ⟨rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (blank)))))), cons true (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R)))))), .E⟩ = some ⟨cons true (rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (blank))))))), rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))), .E⟩ := rfl
  have c10 : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .E⟩ = some ⟨app [] (app [true] L), R, .E⟩ := fun _ _ => rfl
  have h10 : steps ((Z) * 1) ⟨cons true (rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (blank))))))), rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))), .E⟩ = some ⟨rep (Z) [true] (cons true (rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (blank)))))))), cons false (cons true (rep (W) [true] (cons false (R)))), .E⟩ :=
    cross_r trans c10 (Z) (cons true (rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (blank)))))))) (cons false (cons true (rep (W) [true] (cons false (R)))))
  have h11 : steps 2 ⟨rep (Z) [true] (cons true (rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (blank)))))))), cons false (cons true (rep (W) [true] (cons false (R)))), .E⟩ = some ⟨rep (Z) [true] (cons true (rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (blank)))))))), cons false (cons false (rep (W) [true] (cons false (R)))), .F⟩ := rfl
  exact steps_congr trans (a := 5 + (0 + ((k) * 4 + (1 + (0 + ((k) * 2 + (10 + (0 + ((k) * 2 + (1 + ((Z) * 1 + (2)))))))))))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (steps_seq trans h5 (steps_seq trans h6 (steps_seq trans h7 (steps_seq trans h8 (steps_seq trans h9 (steps_seq trans h10 (h11))))))))))))

/-- the same with three 1s left of the head -/
theorem restart3 (W Z k : Nat) (R : Tape) :
    steps (Z + 8 * k + 27) ⟨rep (3) [true] (blank), cons false (cons false (rep (k) [true, false] (cons false (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))))))), .F⟩ = some ⟨rep (Z) [true] (cons true (rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank)))))))))), cons false (cons false (rep (W) [true] (cons false (R)))), .F⟩ := by
  have h0 : steps 9 ⟨rep (3) [true] (blank), cons false (cons false (rep (k) [true, false] (cons false (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))))))), .F⟩ = some ⟨cons false (cons true (cons false (cons true (blank)))), cons false (rep (k) [true, false] (cons false (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R)))))))), .A⟩ := rfl
  have h1 : steps 0 ⟨cons false (cons true (cons false (cons true (blank)))), cons false (rep (k) [true, false] (cons false (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R)))))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (blank)))), rep (k) [false, true] (cons false (cons false (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R)))))))), .A⟩ := by
    simp only [steps_zero, show cons false (rep (k) [true, false] (cons false (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R)))))))) = rep (k) [false, true] (cons false (cons false (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R)))))))) from
      rep_rotate (k) [false] [true, false] [false, true] rfl (cons false (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R)))))))]
  have c2 : ∀ L R : Tape, steps 4 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [false, true] L), R, .A⟩ := fun _ _ => rfl
  have h2 : steps ((k) * 4) ⟨cons false (cons true (cons false (cons true (blank)))), rep (k) [false, true] (cons false (cons false (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R)))))))), .A⟩ = some ⟨rep (k) [false, true] (cons false (cons true (cons false (cons true (blank))))), cons false (cons false (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))))), .A⟩ :=
    cross_r trans c2 (k) (cons false (cons true (cons false (cons true (blank))))) (cons false (cons false (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))))))
  have h3 : steps 1 ⟨rep (k) [false, true] (cons false (cons true (cons false (cons true (blank))))), cons false (cons false (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))))), .A⟩ = some ⟨cons true (rep (k) [false, true] (cons false (cons true (cons false (cons true (blank)))))), cons false (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R)))))), .B⟩ := rfl
  have h4 : steps 0 ⟨cons true (rep (k) [false, true] (cons false (cons true (cons false (cons true (blank)))))), cons false (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R)))))), .B⟩ = some ⟨rep (k) [true, false] (cons true (cons false (cons true (cons false (cons true (blank)))))), cons false (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R)))))), .B⟩ := by
    simp only [steps_zero, show cons true (rep (k) [false, true] (cons false (cons true (cons false (cons true (blank)))))) = rep (k) [true, false] (cons true (cons false (cons true (cons false (cons true (blank)))))) from
      rep_rotate (k) [true] [false, true] [true, false] rfl (cons false (cons true (cons false (cons true (blank)))))]
  have c5 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .B⟩ = some ⟨L, app [false] (app [true, true] R), .B⟩ := fun _ _ => rfl
  have h5 : steps ((k) * 2) ⟨rep (k) [true, false] (cons true (cons false (cons true (cons false (cons true (blank)))))), cons false (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R)))))), .B⟩ = some ⟨cons true (cons false (cons true (cons false (cons true (blank))))), cons false (rep (k) [true, true] (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))))), .B⟩ :=
    cross_l trans c5 (k) (cons true (cons false (cons true (cons false (cons true (blank)))))) (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))))
  have h6 : steps 14 ⟨cons true (cons false (cons true (cons false (cons true (blank))))), cons false (rep (k) [true, true] (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))))), .B⟩ = some ⟨cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank))))))), cons true (rep (k) [true, true] (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))))), .E⟩ := rfl
  have h7 : steps 0 ⟨cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank))))))), cons true (rep (k) [true, true] (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))))), .E⟩ = some ⟨cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank))))))), rep (k) [true, true] (cons true (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))))), .E⟩ := by
    simp only [steps_zero, show cons true (rep (k) [true, true] (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))))) = rep (k) [true, true] (cons true (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))))) from
      rep_rotate (k) [true] [true, true] [true, true] rfl (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))))]
  have c8 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, true] R, .E⟩ = some ⟨app [] (app [true, true] L), R, .E⟩ := fun _ _ => rfl
  have h8 : steps ((k) * 2) ⟨cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank))))))), rep (k) [true, true] (cons true (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))))), .E⟩ = some ⟨rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank)))))))), cons true (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R)))))), .E⟩ :=
    cross_r trans c8 (k) (cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank)))))))) (cons true (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R)))))))
  have h9 : steps 1 ⟨rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank)))))))), cons true (rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R)))))), .E⟩ = some ⟨cons true (rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank))))))))), rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))), .E⟩ := rfl
  have c10 : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .E⟩ = some ⟨app [] (app [true] L), R, .E⟩ := fun _ _ => rfl
  have h10 : steps ((Z) * 1) ⟨cons true (rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank))))))))), rep (Z) [true] (cons false (cons true (rep (W) [true] (cons false (R))))), .E⟩ = some ⟨rep (Z) [true] (cons true (rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank)))))))))), cons false (cons true (rep (W) [true] (cons false (R)))), .E⟩ :=
    cross_r trans c10 (Z) (cons true (rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank)))))))))) (cons false (cons true (rep (W) [true] (cons false (R)))))
  have h11 : steps 2 ⟨rep (Z) [true] (cons true (rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank)))))))))), cons false (cons true (rep (W) [true] (cons false (R)))), .E⟩ = some ⟨rep (Z) [true] (cons true (rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank)))))))))), cons false (cons false (rep (W) [true] (cons false (R)))), .F⟩ := rfl
  exact steps_congr trans (a := 9 + (0 + ((k) * 4 + (1 + (0 + ((k) * 2 + (14 + (0 + ((k) * 2 + (1 + ((Z) * 1 + (2)))))))))))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (steps_seq trans h5 (steps_seq trans h6 (steps_seq trans h7 (steps_seq trans h8 (steps_seq trans h9 (steps_seq trans h10 (h11))))))))))))

/-- the restart at the right end of the tape (last block empty): C comes back -/
theorem tail0 (k : Nat) :
    steps (8 * k + 22) ⟨blank, cons false (cons false (rep (k) [true, false] (cons false (blank)))), .F⟩ = some ⟨rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (blank)))))), cons true (cons true (cons true (cons true (blank)))), .C⟩ := by
  have h0 : steps 5 ⟨blank, cons false (cons false (rep (k) [true, false] (cons false (blank)))), .F⟩ = some ⟨cons false (cons true (blank)), cons false (rep (k) [true, false] (cons false (blank))), .A⟩ := rfl
  have h1 : steps 0 ⟨cons false (cons true (blank)), cons false (rep (k) [true, false] (cons false (blank))), .A⟩ = some ⟨cons false (cons true (blank)), rep (k) [false, true] (cons false (cons false (blank))), .A⟩ := by
    simp only [steps_zero, show cons false (rep (k) [true, false] (cons false (blank))) = rep (k) [false, true] (cons false (cons false (blank))) from
      rep_rotate (k) [false] [true, false] [false, true] rfl (cons false (blank))]
  have c2 : ∀ L R : Tape, steps 4 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [false, true] L), R, .A⟩ := fun _ _ => rfl
  have h2 : steps ((k) * 4) ⟨cons false (cons true (blank)), rep (k) [false, true] (cons false (cons false (blank))), .A⟩ = some ⟨rep (k) [false, true] (cons false (cons true (blank))), cons false (cons false (blank)), .A⟩ :=
    cross_r trans c2 (k) (cons false (cons true (blank))) (cons false (cons false (blank)))
  have h3 : steps 1 ⟨rep (k) [false, true] (cons false (cons true (blank))), cons false (cons false (blank)), .A⟩ = some ⟨cons true (rep (k) [false, true] (cons false (cons true (blank)))), cons false (blank), .B⟩ := rfl
  have h4 : steps 0 ⟨cons true (rep (k) [false, true] (cons false (cons true (blank)))), cons false (blank), .B⟩ = some ⟨rep (k) [true, false] (cons true (cons false (cons true (blank)))), cons false (blank), .B⟩ := by
    simp only [steps_zero, show cons true (rep (k) [false, true] (cons false (cons true (blank)))) = rep (k) [true, false] (cons true (cons false (cons true (blank)))) from
      rep_rotate (k) [true] [false, true] [true, false] rfl (cons false (cons true (blank)))]
  have c5 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .B⟩ = some ⟨L, app [false] (app [true, true] R), .B⟩ := fun _ _ => rfl
  have h5 : steps ((k) * 2) ⟨rep (k) [true, false] (cons true (cons false (cons true (blank)))), cons false (blank), .B⟩ = some ⟨cons true (cons false (cons true (blank))), cons false (rep (k) [true, true] (blank)), .B⟩ :=
    cross_l trans c5 (k) (cons true (cons false (cons true (blank)))) (blank)
  have h6 : steps 10 ⟨cons true (cons false (cons true (blank))), cons false (rep (k) [true, true] (blank)), .B⟩ = some ⟨cons true (cons true (cons true (cons true (cons true (blank))))), cons true (rep (k) [true, true] (blank)), .E⟩ := rfl
  have h7 : steps 0 ⟨cons true (cons true (cons true (cons true (cons true (blank))))), cons true (rep (k) [true, true] (blank)), .E⟩ = some ⟨cons true (cons true (cons true (cons true (cons true (blank))))), rep (k) [true, true] (cons true (blank)), .E⟩ := by
    simp only [steps_zero, show cons true (rep (k) [true, true] (blank)) = rep (k) [true, true] (cons true (blank)) from
      rep_rotate (k) [true] [true, true] [true, true] rfl (blank)]
  have c8 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, true] R, .E⟩ = some ⟨app [] (app [true, true] L), R, .E⟩ := fun _ _ => rfl
  have h8 : steps ((k) * 2) ⟨cons true (cons true (cons true (cons true (cons true (blank))))), rep (k) [true, true] (cons true (blank)), .E⟩ = some ⟨rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (blank)))))), cons true (blank), .E⟩ :=
    cross_r trans c8 (k) (cons true (cons true (cons true (cons true (cons true (blank)))))) (cons true (blank))
  have h9 : steps 6 ⟨rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (blank)))))), cons true (blank), .E⟩ = some ⟨rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (blank)))))), cons true (cons true (cons true (cons true (blank)))), .C⟩ := rfl
  exact steps_congr trans (a := 5 + (0 + ((k) * 4 + (1 + (0 + ((k) * 2 + (10 + (0 + ((k) * 2 + (6)))))))))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (steps_seq trans h5 (steps_seq trans h6 (steps_seq trans h7 (steps_seq trans h8 (h9))))))))))

/-- the restart at the right end of the tape (last block Z + 1) -/
theorem tail1 (Z k : Nat) :
    steps (Z + 8 * k + 23) ⟨blank, cons false (cons false (rep (k) [true, false] (cons false (rep (Z) [true] (cons true (blank)))))), .F⟩ = some ⟨rep (Z) [true] (cons true (rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (blank)))))))), cons true (cons true (cons true (cons true (blank)))), .C⟩ := by
  have h0 : steps 5 ⟨blank, cons false (cons false (rep (k) [true, false] (cons false (rep (Z) [true] (cons true (blank)))))), .F⟩ = some ⟨cons false (cons true (blank)), cons false (rep (k) [true, false] (cons false (rep (Z) [true] (cons true (blank))))), .A⟩ := rfl
  have h1 : steps 0 ⟨cons false (cons true (blank)), cons false (rep (k) [true, false] (cons false (rep (Z) [true] (cons true (blank))))), .A⟩ = some ⟨cons false (cons true (blank)), rep (k) [false, true] (cons false (cons false (rep (Z) [true] (cons true (blank))))), .A⟩ := by
    simp only [steps_zero, show cons false (rep (k) [true, false] (cons false (rep (Z) [true] (cons true (blank))))) = rep (k) [false, true] (cons false (cons false (rep (Z) [true] (cons true (blank))))) from
      rep_rotate (k) [false] [true, false] [false, true] rfl (cons false (rep (Z) [true] (cons true (blank))))]
  have c2 : ∀ L R : Tape, steps 4 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [false, true] L), R, .A⟩ := fun _ _ => rfl
  have h2 : steps ((k) * 4) ⟨cons false (cons true (blank)), rep (k) [false, true] (cons false (cons false (rep (Z) [true] (cons true (blank))))), .A⟩ = some ⟨rep (k) [false, true] (cons false (cons true (blank))), cons false (cons false (rep (Z) [true] (cons true (blank)))), .A⟩ :=
    cross_r trans c2 (k) (cons false (cons true (blank))) (cons false (cons false (rep (Z) [true] (cons true (blank)))))
  have h3 : steps 1 ⟨rep (k) [false, true] (cons false (cons true (blank))), cons false (cons false (rep (Z) [true] (cons true (blank)))), .A⟩ = some ⟨cons true (rep (k) [false, true] (cons false (cons true (blank)))), cons false (rep (Z) [true] (cons true (blank))), .B⟩ := rfl
  have h4 : steps 0 ⟨cons true (rep (k) [false, true] (cons false (cons true (blank)))), cons false (rep (Z) [true] (cons true (blank))), .B⟩ = some ⟨rep (k) [true, false] (cons true (cons false (cons true (blank)))), cons false (rep (Z) [true] (cons true (blank))), .B⟩ := by
    simp only [steps_zero, show cons true (rep (k) [false, true] (cons false (cons true (blank)))) = rep (k) [true, false] (cons true (cons false (cons true (blank)))) from
      rep_rotate (k) [true] [false, true] [true, false] rfl (cons false (cons true (blank)))]
  have c5 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .B⟩ = some ⟨L, app [false] (app [true, true] R), .B⟩ := fun _ _ => rfl
  have h5 : steps ((k) * 2) ⟨rep (k) [true, false] (cons true (cons false (cons true (blank)))), cons false (rep (Z) [true] (cons true (blank))), .B⟩ = some ⟨cons true (cons false (cons true (blank))), cons false (rep (k) [true, true] (rep (Z) [true] (cons true (blank)))), .B⟩ :=
    cross_l trans c5 (k) (cons true (cons false (cons true (blank)))) (rep (Z) [true] (cons true (blank)))
  have h6 : steps 10 ⟨cons true (cons false (cons true (blank))), cons false (rep (k) [true, true] (rep (Z) [true] (cons true (blank)))), .B⟩ = some ⟨cons true (cons true (cons true (cons true (cons true (blank))))), cons true (rep (k) [true, true] (rep (Z) [true] (cons true (blank)))), .E⟩ := rfl
  have h7 : steps 0 ⟨cons true (cons true (cons true (cons true (cons true (blank))))), cons true (rep (k) [true, true] (rep (Z) [true] (cons true (blank)))), .E⟩ = some ⟨cons true (cons true (cons true (cons true (cons true (blank))))), rep (k) [true, true] (cons true (rep (Z) [true] (cons true (blank)))), .E⟩ := by
    simp only [steps_zero, show cons true (rep (k) [true, true] (rep (Z) [true] (cons true (blank)))) = rep (k) [true, true] (cons true (rep (Z) [true] (cons true (blank)))) from
      rep_rotate (k) [true] [true, true] [true, true] rfl (rep (Z) [true] (cons true (blank)))]
  have c8 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, true] R, .E⟩ = some ⟨app [] (app [true, true] L), R, .E⟩ := fun _ _ => rfl
  have h8 : steps ((k) * 2) ⟨cons true (cons true (cons true (cons true (cons true (blank))))), rep (k) [true, true] (cons true (rep (Z) [true] (cons true (blank)))), .E⟩ = some ⟨rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (blank)))))), cons true (rep (Z) [true] (cons true (blank))), .E⟩ :=
    cross_r trans c8 (k) (cons true (cons true (cons true (cons true (cons true (blank)))))) (cons true (rep (Z) [true] (cons true (blank))))
  have h9 : steps 1 ⟨rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (blank)))))), cons true (rep (Z) [true] (cons true (blank))), .E⟩ = some ⟨cons true (rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (blank))))))), rep (Z) [true] (cons true (blank)), .E⟩ := rfl
  have c10 : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .E⟩ = some ⟨app [] (app [true] L), R, .E⟩ := fun _ _ => rfl
  have h10 : steps ((Z) * 1) ⟨cons true (rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (blank))))))), rep (Z) [true] (cons true (blank)), .E⟩ = some ⟨rep (Z) [true] (cons true (rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (blank)))))))), cons true (blank), .E⟩ :=
    cross_r trans c10 (Z) (cons true (rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (blank)))))))) (cons true (blank))
  have h11 : steps 6 ⟨rep (Z) [true] (cons true (rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (blank)))))))), cons true (blank), .E⟩ = some ⟨rep (Z) [true] (cons true (rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (blank)))))))), cons true (cons true (cons true (cons true (blank)))), .C⟩ := rfl
  exact steps_congr trans (a := 5 + (0 + ((k) * 4 + (1 + (0 + ((k) * 2 + (10 + (0 + ((k) * 2 + (1 + ((Z) * 1 + (6)))))))))))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (steps_seq trans h5 (steps_seq trans h6 (steps_seq trans h7 (steps_seq trans h8 (steps_seq trans h9 (steps_seq trans h10 (h11))))))))))))

/-- the same with three 1s left of the head, last block empty -/
theorem tail30 (k : Nat) :
    steps (8 * k + 30) ⟨rep (3) [true] (blank), cons false (cons false (rep (k) [true, false] (cons false (blank)))), .F⟩ = some ⟨rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank)))))))), cons true (cons true (cons true (cons true (blank)))), .C⟩ := by
  have h0 : steps 9 ⟨rep (3) [true] (blank), cons false (cons false (rep (k) [true, false] (cons false (blank)))), .F⟩ = some ⟨cons false (cons true (cons false (cons true (blank)))), cons false (rep (k) [true, false] (cons false (blank))), .A⟩ := rfl
  have h1 : steps 0 ⟨cons false (cons true (cons false (cons true (blank)))), cons false (rep (k) [true, false] (cons false (blank))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (blank)))), rep (k) [false, true] (cons false (cons false (blank))), .A⟩ := by
    simp only [steps_zero, show cons false (rep (k) [true, false] (cons false (blank))) = rep (k) [false, true] (cons false (cons false (blank))) from
      rep_rotate (k) [false] [true, false] [false, true] rfl (cons false (blank))]
  have c2 : ∀ L R : Tape, steps 4 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [false, true] L), R, .A⟩ := fun _ _ => rfl
  have h2 : steps ((k) * 4) ⟨cons false (cons true (cons false (cons true (blank)))), rep (k) [false, true] (cons false (cons false (blank))), .A⟩ = some ⟨rep (k) [false, true] (cons false (cons true (cons false (cons true (blank))))), cons false (cons false (blank)), .A⟩ :=
    cross_r trans c2 (k) (cons false (cons true (cons false (cons true (blank))))) (cons false (cons false (blank)))
  have h3 : steps 1 ⟨rep (k) [false, true] (cons false (cons true (cons false (cons true (blank))))), cons false (cons false (blank)), .A⟩ = some ⟨cons true (rep (k) [false, true] (cons false (cons true (cons false (cons true (blank)))))), cons false (blank), .B⟩ := rfl
  have h4 : steps 0 ⟨cons true (rep (k) [false, true] (cons false (cons true (cons false (cons true (blank)))))), cons false (blank), .B⟩ = some ⟨rep (k) [true, false] (cons true (cons false (cons true (cons false (cons true (blank)))))), cons false (blank), .B⟩ := by
    simp only [steps_zero, show cons true (rep (k) [false, true] (cons false (cons true (cons false (cons true (blank)))))) = rep (k) [true, false] (cons true (cons false (cons true (cons false (cons true (blank)))))) from
      rep_rotate (k) [true] [false, true] [true, false] rfl (cons false (cons true (cons false (cons true (blank)))))]
  have c5 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .B⟩ = some ⟨L, app [false] (app [true, true] R), .B⟩ := fun _ _ => rfl
  have h5 : steps ((k) * 2) ⟨rep (k) [true, false] (cons true (cons false (cons true (cons false (cons true (blank)))))), cons false (blank), .B⟩ = some ⟨cons true (cons false (cons true (cons false (cons true (blank))))), cons false (rep (k) [true, true] (blank)), .B⟩ :=
    cross_l trans c5 (k) (cons true (cons false (cons true (cons false (cons true (blank)))))) (blank)
  have h6 : steps 14 ⟨cons true (cons false (cons true (cons false (cons true (blank))))), cons false (rep (k) [true, true] (blank)), .B⟩ = some ⟨cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank))))))), cons true (rep (k) [true, true] (blank)), .E⟩ := rfl
  have h7 : steps 0 ⟨cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank))))))), cons true (rep (k) [true, true] (blank)), .E⟩ = some ⟨cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank))))))), rep (k) [true, true] (cons true (blank)), .E⟩ := by
    simp only [steps_zero, show cons true (rep (k) [true, true] (blank)) = rep (k) [true, true] (cons true (blank)) from
      rep_rotate (k) [true] [true, true] [true, true] rfl (blank)]
  have c8 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, true] R, .E⟩ = some ⟨app [] (app [true, true] L), R, .E⟩ := fun _ _ => rfl
  have h8 : steps ((k) * 2) ⟨cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank))))))), rep (k) [true, true] (cons true (blank)), .E⟩ = some ⟨rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank)))))))), cons true (blank), .E⟩ :=
    cross_r trans c8 (k) (cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank)))))))) (cons true (blank))
  have h9 : steps 6 ⟨rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank)))))))), cons true (blank), .E⟩ = some ⟨rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank)))))))), cons true (cons true (cons true (cons true (blank)))), .C⟩ := rfl
  exact steps_congr trans (a := 9 + (0 + ((k) * 4 + (1 + (0 + ((k) * 2 + (14 + (0 + ((k) * 2 + (6)))))))))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (steps_seq trans h5 (steps_seq trans h6 (steps_seq trans h7 (steps_seq trans h8 (h9))))))))))

/-- the same with three 1s left of the head, last block Z + 1 -/
theorem tail31 (Z k : Nat) :
    steps (Z + 8 * k + 31) ⟨rep (3) [true] (blank), cons false (cons false (rep (k) [true, false] (cons false (rep (Z) [true] (cons true (blank)))))), .F⟩ = some ⟨rep (Z) [true] (cons true (rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank)))))))))), cons true (cons true (cons true (cons true (blank)))), .C⟩ := by
  have h0 : steps 9 ⟨rep (3) [true] (blank), cons false (cons false (rep (k) [true, false] (cons false (rep (Z) [true] (cons true (blank)))))), .F⟩ = some ⟨cons false (cons true (cons false (cons true (blank)))), cons false (rep (k) [true, false] (cons false (rep (Z) [true] (cons true (blank))))), .A⟩ := rfl
  have h1 : steps 0 ⟨cons false (cons true (cons false (cons true (blank)))), cons false (rep (k) [true, false] (cons false (rep (Z) [true] (cons true (blank))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (blank)))), rep (k) [false, true] (cons false (cons false (rep (Z) [true] (cons true (blank))))), .A⟩ := by
    simp only [steps_zero, show cons false (rep (k) [true, false] (cons false (rep (Z) [true] (cons true (blank))))) = rep (k) [false, true] (cons false (cons false (rep (Z) [true] (cons true (blank))))) from
      rep_rotate (k) [false] [true, false] [false, true] rfl (cons false (rep (Z) [true] (cons true (blank))))]
  have c2 : ∀ L R : Tape, steps 4 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [false, true] L), R, .A⟩ := fun _ _ => rfl
  have h2 : steps ((k) * 4) ⟨cons false (cons true (cons false (cons true (blank)))), rep (k) [false, true] (cons false (cons false (rep (Z) [true] (cons true (blank))))), .A⟩ = some ⟨rep (k) [false, true] (cons false (cons true (cons false (cons true (blank))))), cons false (cons false (rep (Z) [true] (cons true (blank)))), .A⟩ :=
    cross_r trans c2 (k) (cons false (cons true (cons false (cons true (blank))))) (cons false (cons false (rep (Z) [true] (cons true (blank)))))
  have h3 : steps 1 ⟨rep (k) [false, true] (cons false (cons true (cons false (cons true (blank))))), cons false (cons false (rep (Z) [true] (cons true (blank)))), .A⟩ = some ⟨cons true (rep (k) [false, true] (cons false (cons true (cons false (cons true (blank)))))), cons false (rep (Z) [true] (cons true (blank))), .B⟩ := rfl
  have h4 : steps 0 ⟨cons true (rep (k) [false, true] (cons false (cons true (cons false (cons true (blank)))))), cons false (rep (Z) [true] (cons true (blank))), .B⟩ = some ⟨rep (k) [true, false] (cons true (cons false (cons true (cons false (cons true (blank)))))), cons false (rep (Z) [true] (cons true (blank))), .B⟩ := by
    simp only [steps_zero, show cons true (rep (k) [false, true] (cons false (cons true (cons false (cons true (blank)))))) = rep (k) [true, false] (cons true (cons false (cons true (cons false (cons true (blank)))))) from
      rep_rotate (k) [true] [false, true] [true, false] rfl (cons false (cons true (cons false (cons true (blank)))))]
  have c5 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .B⟩ = some ⟨L, app [false] (app [true, true] R), .B⟩ := fun _ _ => rfl
  have h5 : steps ((k) * 2) ⟨rep (k) [true, false] (cons true (cons false (cons true (cons false (cons true (blank)))))), cons false (rep (Z) [true] (cons true (blank))), .B⟩ = some ⟨cons true (cons false (cons true (cons false (cons true (blank))))), cons false (rep (k) [true, true] (rep (Z) [true] (cons true (blank)))), .B⟩ :=
    cross_l trans c5 (k) (cons true (cons false (cons true (cons false (cons true (blank)))))) (rep (Z) [true] (cons true (blank)))
  have h6 : steps 14 ⟨cons true (cons false (cons true (cons false (cons true (blank))))), cons false (rep (k) [true, true] (rep (Z) [true] (cons true (blank)))), .B⟩ = some ⟨cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank))))))), cons true (rep (k) [true, true] (rep (Z) [true] (cons true (blank)))), .E⟩ := rfl
  have h7 : steps 0 ⟨cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank))))))), cons true (rep (k) [true, true] (rep (Z) [true] (cons true (blank)))), .E⟩ = some ⟨cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank))))))), rep (k) [true, true] (cons true (rep (Z) [true] (cons true (blank)))), .E⟩ := by
    simp only [steps_zero, show cons true (rep (k) [true, true] (rep (Z) [true] (cons true (blank)))) = rep (k) [true, true] (cons true (rep (Z) [true] (cons true (blank)))) from
      rep_rotate (k) [true] [true, true] [true, true] rfl (rep (Z) [true] (cons true (blank)))]
  have c8 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, true] R, .E⟩ = some ⟨app [] (app [true, true] L), R, .E⟩ := fun _ _ => rfl
  have h8 : steps ((k) * 2) ⟨cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank))))))), rep (k) [true, true] (cons true (rep (Z) [true] (cons true (blank)))), .E⟩ = some ⟨rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank)))))))), cons true (rep (Z) [true] (cons true (blank))), .E⟩ :=
    cross_r trans c8 (k) (cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank)))))))) (cons true (rep (Z) [true] (cons true (blank))))
  have h9 : steps 1 ⟨rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank)))))))), cons true (rep (Z) [true] (cons true (blank))), .E⟩ = some ⟨cons true (rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank))))))))), rep (Z) [true] (cons true (blank)), .E⟩ := rfl
  have c10 : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .E⟩ = some ⟨app [] (app [true] L), R, .E⟩ := fun _ _ => rfl
  have h10 : steps ((Z) * 1) ⟨cons true (rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank))))))))), rep (Z) [true] (cons true (blank)), .E⟩ = some ⟨rep (Z) [true] (cons true (rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank)))))))))), cons true (blank), .E⟩ :=
    cross_r trans c10 (Z) (cons true (rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank)))))))))) (cons true (blank))
  have h11 : steps 6 ⟨rep (Z) [true] (cons true (rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank)))))))))), cons true (blank), .E⟩ = some ⟨rep (Z) [true] (cons true (rep (k) [true, true] (cons true (cons true (cons true (cons true (cons true (cons true (cons true (blank)))))))))), cons true (cons true (cons true (cons true (blank)))), .C⟩ := rfl
  exact steps_congr trans (a := 9 + (0 + ((k) * 4 + (1 + (0 + ((k) * 2 + (14 + (0 + ((k) * 2 + (1 + ((Z) * 1 + (6)))))))))))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (steps_seq trans h5 (steps_seq trans h6 (steps_seq trans h7 (steps_seq trans h8 (steps_seq trans h9 (steps_seq trans h10 (h11))))))))))))

/-- C at the right end turns into the new start: a block of n + 4 and a block of 3 -/
theorem cback (n : Nat) :
    steps (5) ⟨rep (5) [true] (rep (n) [true] (blank)), cons true (cons true (cons true (cons true (blank)))), .C⟩ = some ⟨cons true (rep (3) [true] (rep (n) [true] (blank))), cons false (cons false (cons true (cons true (cons true (blank))))), .F⟩ := by
  have h0 : steps 5 ⟨rep (5) [true] (rep (n) [true] (blank)), cons true (cons true (cons true (cons true (blank)))), .C⟩ = some ⟨cons true (rep (3) [true] (rep (n) [true] (blank))), cons false (cons false (cons true (cons true (cons true (blank))))), .F⟩ := rfl
  exact steps_congr trans (a := 5) (by omega) (h0)

/-- two 1s left of the head and a unit right of the gap: the unit is cleared, the left block becomes 5 -/
theorem two1 (R : Tape) :
    steps (15) ⟨rep (2) [true] (blank), cons false (cons false (cons true (cons false (R)))), .F⟩ = some ⟨cons true (cons true (cons true (cons true (cons true (blank))))), cons false (cons false (cons false (R))), .F⟩ := by
  have h0 : steps 15 ⟨rep (2) [true] (blank), cons false (cons false (cons true (cons false (R)))), .F⟩ = some ⟨cons true (cons true (cons true (cons true (cons true (blank))))), cons false (cons false (cons false (R))), .F⟩ := rfl
  exact steps_congr trans (a := 15) (by omega) (h0)

/-- two 1s left of the head and a block of Y + 2: it loses one 1, the left block becomes 5 -/
theorem two2 (Y : Nat) (R : Tape) :
    steps (15) ⟨rep (2) [true] (blank), cons false (cons false (cons true (cons true (rep (Y) [true] (cons false (R)))))), .F⟩ = some ⟨cons true (cons true (cons true (cons true (cons true (blank))))), cons false (cons false (cons true (rep (Y) [true] (cons false (R))))), .F⟩ := by
  have h0 : steps 15 ⟨rep (2) [true] (blank), cons false (cons false (cons true (cons true (rep (Y) [true] (cons false (R)))))), .F⟩ = some ⟨cons true (cons true (cons true (cons true (cons true (blank))))), cons false (cons false (cons true (rep (Y) [true] (cons false (R))))), .F⟩ := rfl
  exact steps_congr trans (a := 15) (by omega) (h0)

/-- four 1s left of the head, units and then blank tape: D comes to read a 0 -/
theorem haltcfg (k : Nat) :
    steps (6 * k + 17) ⟨rep (4) [true] (blank), cons false (cons false (rep (k) [true, false] (blank))), .F⟩ = some ⟨blank, cons false (cons false (cons true (cons true (cons true (cons true (cons true (rep (k) [true, true] (cons true (blank))))))))), .D⟩ := by
  have h0 : steps 9 ⟨rep (4) [true] (blank), cons false (cons false (rep (k) [true, false] (blank))), .F⟩ = some ⟨cons false (cons true (cons false (cons true (rep (1) [true] (blank))))), cons false (rep (k) [true, false] (blank)), .A⟩ := rfl
  have h1 : steps 0 ⟨cons false (cons true (cons false (cons true (rep (1) [true] (blank))))), cons false (rep (k) [true, false] (blank)), .A⟩ = some ⟨cons false (cons true (cons false (cons true (rep (1) [true] (blank))))), rep (k) [false, true] (cons false (blank)), .A⟩ := by
    simp only [steps_zero, show cons false (rep (k) [true, false] (blank)) = rep (k) [false, true] (cons false (blank)) from
      rep_rotate (k) [false] [true, false] [false, true] rfl (blank)]
  have c2 : ∀ L R : Tape, steps 4 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [false, true] L), R, .A⟩ := fun _ _ => rfl
  have h2 : steps ((k) * 4) ⟨cons false (cons true (cons false (cons true (rep (1) [true] (blank))))), rep (k) [false, true] (cons false (blank)), .A⟩ = some ⟨rep (k) [false, true] (cons false (cons true (cons false (cons true (rep (1) [true] (blank)))))), cons false (blank), .A⟩ :=
    cross_r trans c2 (k) (cons false (cons true (cons false (cons true (rep (1) [true] (blank)))))) (cons false (blank))
  have h3 : steps 2 ⟨rep (k) [false, true] (cons false (cons true (cons false (cons true (rep (1) [true] (blank)))))), cons false (blank), .A⟩ = some ⟨rep (k) [false, true] (cons false (cons true (cons false (cons true (rep (1) [true] (blank)))))), cons true (cons true (blank)), .C⟩ := rfl
  have c4 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .C⟩ = some ⟨L, app [true] (app [true, true] R), .C⟩ := fun _ _ => rfl
  have h4 : steps ((k) * 2) ⟨rep (k) [false, true] (cons false (cons true (cons false (cons true (rep (1) [true] (blank)))))), cons true (cons true (blank)), .C⟩ = some ⟨cons false (cons true (cons false (cons true (rep (1) [true] (blank))))), cons true (rep (k) [true, true] (cons true (blank))), .C⟩ :=
    cross_l trans c4 (k) (cons false (cons true (cons false (cons true (rep (1) [true] (blank)))))) (cons true (blank))
  have h5 : steps 6 ⟨cons false (cons true (cons false (cons true (rep (1) [true] (blank))))), cons true (rep (k) [true, true] (cons true (blank))), .C⟩ = some ⟨blank, cons false (cons false (cons true (cons true (cons true (cons true (cons true (rep (k) [true, true] (cons true (blank))))))))), .D⟩ := rfl
  exact steps_congr trans (a := 9 + (0 + ((k) * 4 + (2 + ((k) * 2 + (6)))))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (h5))))))

end H15252
