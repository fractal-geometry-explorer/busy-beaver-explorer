import Machine

/-! Bounce rules of the reflector Q of 1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---, written by `py/gen_walk.py` with `bbtools.symtm.prove`. -/

namespace H71372

open TM

/-- One bounce with Q in its short form: `L (01)^(c+1) 0 (01)^(a+1) E>` becomes `L (01)^c 1 (01)^(a+3) E>` (stated as the run writes it). -/
theorem bounce0_cells (a c : Nat) (L : Tape) :
    steps (4 * a + 14) ⟨rep (a + 1) [true, false] (cons false (rep (c + 1) [true, false] (L))), blank, .E⟩ = some ⟨cons true (cons false (cons true (rep (a) [false, true] (cons false (cons true (cons false (cons true (rep (c) [true, false] (L))))))))), blank, .E⟩ := by
  have h0 : steps 2 ⟨rep (a + 1) [true, false] (cons false (rep (c + 1) [true, false] (L))), blank, .E⟩ = some ⟨rep (a) [true, false] (cons false (rep (c + 1) [true, false] (L))), cons false (cons false (cons true (blank))), .E⟩ := rfl
  have c1 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .E⟩ = some ⟨L, app [false] (app [false, true] R), .E⟩ := fun _ _ => rfl
  have h1 : steps ((a) * 2) ⟨rep (a) [true, false] (cons false (rep (c + 1) [true, false] (L))), cons false (cons false (cons true (blank))), .E⟩ = some ⟨cons false (rep (c + 1) [true, false] (L)), cons false (rep (a) [false, true] (cons false (cons true (blank)))), .E⟩ :=
    cross_l trans c1 (a) (cons false (rep (c + 1) [true, false] (L))) (cons false (cons true (blank)))
  have h2 : steps 9 ⟨cons false (rep (c + 1) [true, false] (L)), cons false (rep (a) [false, true] (cons false (cons true (blank)))), .E⟩ = some ⟨cons false (cons true (cons false (cons true (rep (c) [true, false] (L))))), rep (a) [false, true] (cons false (cons true (blank))), .D⟩ := rfl
  have c3 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .D⟩ = some ⟨app [] (app [false, true] L), R, .D⟩ := fun _ _ => rfl
  have h3 : steps ((a) * 2) ⟨cons false (cons true (cons false (cons true (rep (c) [true, false] (L))))), rep (a) [false, true] (cons false (cons true (blank))), .D⟩ = some ⟨rep (a) [false, true] (cons false (cons true (cons false (cons true (rep (c) [true, false] (L)))))), cons false (cons true (blank)), .D⟩ :=
    cross_r trans c3 (a) (cons false (cons true (cons false (cons true (rep (c) [true, false] (L)))))) (cons false (cons true (blank)))
  have h4 : steps 3 ⟨rep (a) [false, true] (cons false (cons true (cons false (cons true (rep (c) [true, false] (L)))))), cons false (cons true (blank)), .D⟩ = some ⟨cons true (cons false (cons true (rep (a) [false, true] (cons false (cons true (cons false (cons true (rep (c) [true, false] (L))))))))), blank, .E⟩ := rfl
  exact steps_congr trans (a := 2 + ((a) * 2 + (9 + ((a) * 2 + (3))))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

/-- One bounce with Q in its long form: `L (01)^(c+1) 1 (01)^(a+1) E>` becomes `L (01)^c 0 (01)^(a+3) E>` (stated as the run writes it). -/
theorem bounce1_cells (a c : Nat) (L : Tape) :
    steps (4 * a + 10) ⟨rep (a + 1) [true, false] (cons true (rep (c + 1) [true, false] (L))), blank, .E⟩ = some ⟨cons true (cons false (cons true (rep (a) [false, true] (cons false (cons true (cons false (cons false (rep (c) [true, false] (L))))))))), blank, .E⟩ := by
  have h0 : steps 2 ⟨rep (a + 1) [true, false] (cons true (rep (c + 1) [true, false] (L))), blank, .E⟩ = some ⟨rep (a) [true, false] (cons true (rep (c + 1) [true, false] (L))), cons false (cons false (cons true (blank))), .E⟩ := rfl
  have c1 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .E⟩ = some ⟨L, app [false] (app [false, true] R), .E⟩ := fun _ _ => rfl
  have h1 : steps ((a) * 2) ⟨rep (a) [true, false] (cons true (rep (c + 1) [true, false] (L))), cons false (cons false (cons true (blank))), .E⟩ = some ⟨cons true (rep (c + 1) [true, false] (L)), cons false (rep (a) [false, true] (cons false (cons true (blank)))), .E⟩ :=
    cross_l trans c1 (a) (cons true (rep (c + 1) [true, false] (L))) (cons false (cons true (blank)))
  have h2 : steps 5 ⟨cons true (rep (c + 1) [true, false] (L)), cons false (rep (a) [false, true] (cons false (cons true (blank)))), .E⟩ = some ⟨cons false (cons true (cons false (cons false (rep (c) [true, false] (L))))), rep (a) [false, true] (cons false (cons true (blank))), .D⟩ := rfl
  have c3 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .D⟩ = some ⟨app [] (app [false, true] L), R, .D⟩ := fun _ _ => rfl
  have h3 : steps ((a) * 2) ⟨cons false (cons true (cons false (cons false (rep (c) [true, false] (L))))), rep (a) [false, true] (cons false (cons true (blank))), .D⟩ = some ⟨rep (a) [false, true] (cons false (cons true (cons false (cons false (rep (c) [true, false] (L)))))), cons false (cons true (blank)), .D⟩ :=
    cross_r trans c3 (a) (cons false (cons true (cons false (cons false (rep (c) [true, false] (L)))))) (cons false (cons true (blank)))
  have h4 : steps 3 ⟨rep (a) [false, true] (cons false (cons true (cons false (cons false (rep (c) [true, false] (L)))))), cons false (cons true (blank)), .D⟩ = some ⟨cons true (cons false (cons true (rep (a) [false, true] (cons false (cons true (cons false (cons false (rep (c) [true, false] (L))))))))), blank, .E⟩ := rfl
  exact steps_congr trans (a := 2 + ((a) * 2 + (5 + ((a) * 2 + (3))))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

end H71372
