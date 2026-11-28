import Machine

/-! Mover rules of 1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---, written by `py/gen_movers.py` with `bbtools.symtm.prove`. -/

namespace H71372

open TM

/-- The left sweep crosses a mover at rest: `L 0 0 1 1 0 (01)^(n+1) E> 0 R` becomes `L E> 0 0 1 0 1 1 (01)^(n+1) R`. -/
theorem lm_cells (n : Nat) (L R : Tape) :
    steps (2 * n + 17) ⟨rep (n + 1) [true, false] (cons false (cons true (cons true (cons false (cons false (L)))))), cons false (R), .E⟩ = some ⟨L, cons false (cons false (cons true (cons false (cons true (cons true (rep (n + 1) [false, true] (R))))))), .E⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .E⟩ = some ⟨L, app [false] (app [false, true] R), .E⟩ := fun _ _ => rfl
  have h0 : steps ((n + 1) * 2) ⟨rep (n + 1) [true, false] (cons false (cons true (cons true (cons false (cons false (L)))))), cons false (R), .E⟩ = some ⟨cons false (cons true (cons true (cons false (cons false (L))))), cons false (rep (n + 1) [false, true] (R)), .E⟩ :=
    cross_l trans c0 (n + 1) (cons false (cons true (cons true (cons false (cons false (L)))))) (R)
  have h1 : steps 15 ⟨cons false (cons true (cons true (cons false (cons false (L))))), cons false (rep (n + 1) [false, true] (R)), .E⟩ = some ⟨L, cons false (cons false (cons true (cons false (cons true (cons true (rep (n + 1) [false, true] (R))))))), .E⟩ := rfl
  exact steps_congr trans (a := (n + 1) * 2 + (15)) (by omega) (steps_seq trans h0 (h1))

/-- The right sweep crosses a swept mover: `L D> 0 1 0 1 1 (01)^(n+2) R` becomes `L 1 0 1 0 0 1 1 0 0 (10)^n D> R`. -/
theorem rm_cells (n : Nat) (L R : Tape) :
    steps (2 * n + 9) ⟨L, cons false (cons true (cons false (cons true (cons true (rep (n + 2) [false, true] (R)))))), .D⟩ = some ⟨rep (n) [false, true] (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (L)))))))))), R, .D⟩ := by
  have h0 : steps 9 ⟨L, cons false (cons true (cons false (cons true (cons true (rep (n + 2) [false, true] (R)))))), .D⟩ = some ⟨cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (L))))))))), rep (n) [false, true] (R), .D⟩ := rfl
  have c1 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .D⟩ = some ⟨app [] (app [false, true] L), R, .D⟩ := fun _ _ => rfl
  have h1 : steps ((n) * 2) ⟨cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (L))))))))), rep (n) [false, true] (R), .D⟩ = some ⟨rep (n) [false, true] (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (L)))))))))), R, .D⟩ :=
    cross_r trans c1 (n) (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (L)))))))))) (R)
  exact steps_congr trans (a := 9 + ((n) * 2)) (by omega) (steps_seq trans h0 (h1))

/-- The right sweep crosses a swept mover with a one-pair gap and comes out in state F. -/
theorem rm1_cells (L R : Tape) :
    steps (7) ⟨L, cons false (cons true (cons false (cons true (cons true (cons false (cons true (R))))))), .D⟩ = some ⟨cons true (cons true (cons false (cons false (cons true (cons false (cons true (L))))))), R, .F⟩ := by
  have h0 : steps 7 ⟨L, cons false (cons true (cons false (cons true (cons true (cons false (cons true (R))))))), .D⟩ = some ⟨cons true (cons true (cons false (cons false (cons true (cons false (cons true (L))))))), R, .F⟩ := rfl
  exact steps_congr trans (a := 7) (by omega) (h0)

/-- In state F the right sweep crosses a swept mover with a one-pair gap and stays in F. -/
theorem fm1_cells (L R : Tape) :
    steps (7) ⟨L, cons false (cons true (cons false (cons true (cons true (cons false (cons true (R))))))), .F⟩ = some ⟨cons true (cons true (cons false (cons false (cons true (cons false (cons false (L))))))), R, .F⟩ := by
  have h0 : steps 7 ⟨L, cons false (cons true (cons false (cons true (cons true (cons false (cons true (R))))))), .F⟩ = some ⟨cons true (cons true (cons false (cons false (cons true (cons false (cons false (L))))))), R, .F⟩ := rfl
  exact steps_congr trans (a := 7) (by omega) (h0)

/-- In state F the right sweep crosses a swept mover with a longer gap and comes out in state D. -/
theorem fm_cells (n : Nat) (L R : Tape) :
    steps (2 * n + 9) ⟨L, cons false (cons true (cons false (cons true (cons true (rep (n + 2) [false, true] (R)))))), .F⟩ = some ⟨rep (n) [false, true] (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons false (L)))))))))), R, .D⟩ := by
  have h0 : steps 9 ⟨L, cons false (cons true (cons false (cons true (cons true (rep (n + 2) [false, true] (R)))))), .F⟩ = some ⟨cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons false (L))))))))), rep (n) [false, true] (R), .D⟩ := rfl
  have c1 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .D⟩ = some ⟨app [] (app [false, true] L), R, .D⟩ := fun _ _ => rfl
  have h1 : steps ((n) * 2) ⟨cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons false (L))))))))), rep (n) [false, true] (R), .D⟩ = some ⟨rep (n) [false, true] (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons false (L)))))))))), R, .D⟩ :=
    cross_r trans c1 (n) (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons false (L)))))))))) (R)
  exact steps_congr trans (a := 9 + ((n) * 2)) (by omega) (steps_seq trans h0 (h1))

/-- The left sweep turns at Q in its short form, whatever lies on the right. -/
theorem qr0_cells (a c : Nat) (L R : Tape) :
    steps (4 * a + 13) ⟨rep (a + 1) [true, false] (cons false (rep (c + 1) [true, false] (L))), cons false (R), .E⟩ = some ⟨rep (a + 1) [false, true] (cons false (cons true (cons false (cons true (rep (c) [true, false] (L)))))), R, .D⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .E⟩ = some ⟨L, app [false] (app [false, true] R), .E⟩ := fun _ _ => rfl
  have h0 : steps ((a + 1) * 2) ⟨rep (a + 1) [true, false] (cons false (rep (c + 1) [true, false] (L))), cons false (R), .E⟩ = some ⟨cons false (rep (c + 1) [true, false] (L)), cons false (rep (a + 1) [false, true] (R)), .E⟩ :=
    cross_l trans c0 (a + 1) (cons false (rep (c + 1) [true, false] (L))) (R)
  have h1 : steps 9 ⟨cons false (rep (c + 1) [true, false] (L)), cons false (rep (a + 1) [false, true] (R)), .E⟩ = some ⟨cons false (cons true (cons false (cons true (rep (c) [true, false] (L))))), rep (a + 1) [false, true] (R), .D⟩ := rfl
  have c2 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .D⟩ = some ⟨app [] (app [false, true] L), R, .D⟩ := fun _ _ => rfl
  have h2 : steps ((a + 1) * 2) ⟨cons false (cons true (cons false (cons true (rep (c) [true, false] (L))))), rep (a + 1) [false, true] (R), .D⟩ = some ⟨rep (a + 1) [false, true] (cons false (cons true (cons false (cons true (rep (c) [true, false] (L)))))), R, .D⟩ :=
    cross_r trans c2 (a + 1) (cons false (cons true (cons false (cons true (rep (c) [true, false] (L)))))) (R)
  exact steps_congr trans (a := (a + 1) * 2 + (9 + ((a + 1) * 2))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (h2)))

/-- The left sweep turns at Q in its long form, whatever lies on the right. -/
theorem qr1_cells (a c : Nat) (L R : Tape) :
    steps (4 * a + 9) ⟨rep (a + 1) [true, false] (cons true (rep (c + 1) [true, false] (L))), cons false (R), .E⟩ = some ⟨rep (a + 1) [false, true] (cons false (cons true (cons false (cons false (rep (c) [true, false] (L)))))), R, .D⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .E⟩ = some ⟨L, app [false] (app [false, true] R), .E⟩ := fun _ _ => rfl
  have h0 : steps ((a + 1) * 2) ⟨rep (a + 1) [true, false] (cons true (rep (c + 1) [true, false] (L))), cons false (R), .E⟩ = some ⟨cons true (rep (c + 1) [true, false] (L)), cons false (rep (a + 1) [false, true] (R)), .E⟩ :=
    cross_l trans c0 (a + 1) (cons true (rep (c + 1) [true, false] (L))) (R)
  have h1 : steps 5 ⟨cons true (rep (c + 1) [true, false] (L)), cons false (rep (a + 1) [false, true] (R)), .E⟩ = some ⟨cons false (cons true (cons false (cons false (rep (c) [true, false] (L))))), rep (a + 1) [false, true] (R), .D⟩ := rfl
  have c2 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .D⟩ = some ⟨app [] (app [false, true] L), R, .D⟩ := fun _ _ => rfl
  have h2 : steps ((a + 1) * 2) ⟨cons false (cons true (cons false (cons false (rep (c) [true, false] (L))))), rep (a + 1) [false, true] (R), .D⟩ = some ⟨rep (a + 1) [false, true] (cons false (cons true (cons false (cons false (rep (c) [true, false] (L)))))), R, .D⟩ :=
    cross_r trans c2 (a + 1) (cons false (cons true (cons false (cons false (rep (c) [true, false] (L)))))) (R)
  exact steps_congr trans (a := (a + 1) * 2 + (5 + ((a + 1) * 2))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (h2)))

end H71372
