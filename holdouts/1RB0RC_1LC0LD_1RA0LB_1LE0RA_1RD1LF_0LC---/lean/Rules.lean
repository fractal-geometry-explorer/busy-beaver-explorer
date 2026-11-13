import Machine

/-! Cell-level rules of 1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RD1LF_0LC---, written by `py/gen_rules.py` with `bbtools.symtm.prove`. -/

namespace H54407

open TM

/-- One bounce with Q in its short form: `1 A>1 0 (10)^a 0 (10)^(c+2)` becomes `1 A>1 0 (10)^(a+2) 1 1 0 (10)^c` (written as the run leaves it). -/
theorem bounce0_cells (a c : Nat) (R : Tape) :
    steps (4 * a + 14) ⟨cons true (blank), cons true (cons false (rep (a) [true, false] (cons false (rep (c + 2) [true, false] (R))))), .A⟩ = some ⟨cons true (blank), cons true (cons false (cons true (cons false (cons true (rep (a) [false, true] (cons false (cons true (rep (c + 1) [true, false] (R))))))))), .A⟩ := by
  have h0 : steps 2 ⟨cons true (blank), cons true (cons false (rep (a) [true, false] (cons false (rep (c + 2) [true, false] (R))))), .A⟩ = some ⟨cons true (cons false (cons true (blank))), rep (a) [true, false] (cons false (rep (c + 2) [true, false] (R))), .A⟩ := rfl
  have c1 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, false] R, .A⟩ = some ⟨app [] (app [true, false] L), R, .A⟩ := fun _ _ => rfl
  have h1 : steps ((a) * 2) ⟨cons true (cons false (cons true (blank))), rep (a) [true, false] (cons false (rep (c + 2) [true, false] (R))), .A⟩ = some ⟨rep (a) [true, false] (cons true (cons false (cons true (blank)))), cons false (rep (c + 2) [true, false] (R)), .A⟩ :=
    cross_r trans c1 (a) (cons true (cons false (cons true (blank)))) (cons false (rep (c + 2) [true, false] (R)))
  have h2 : steps 6 ⟨rep (a) [true, false] (cons true (cons false (cons true (blank)))), cons false (rep (c + 2) [true, false] (R)), .A⟩ = some ⟨rep (a) [true, false] (cons true (cons false (cons true (blank)))), cons false (cons false (cons true (rep (c + 1) [true, false] (R)))), .B⟩ := rfl
  have c3 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .B⟩ = some ⟨L, app [false] (app [false, true] R), .B⟩ := fun _ _ => rfl
  have h3 : steps ((a) * 2) ⟨rep (a) [true, false] (cons true (cons false (cons true (blank)))), cons false (cons false (cons true (rep (c + 1) [true, false] (R)))), .B⟩ = some ⟨cons true (cons false (cons true (blank))), cons false (rep (a) [false, true] (cons false (cons true (rep (c + 1) [true, false] (R))))), .B⟩ :=
    cross_l trans c3 (a) (cons true (cons false (cons true (blank)))) (cons false (cons true (rep (c + 1) [true, false] (R))))
  have h4 : steps 6 ⟨cons true (cons false (cons true (blank))), cons false (rep (a) [false, true] (cons false (cons true (rep (c + 1) [true, false] (R))))), .B⟩ = some ⟨cons true (blank), cons true (cons false (cons true (cons false (cons true (rep (a) [false, true] (cons false (cons true (rep (c + 1) [true, false] (R))))))))), .A⟩ := rfl
  exact steps_congr trans (a := 2 + ((a) * 2 + (6 + ((a) * 2 + (6))))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

/-- One bounce with Q in its long form: `1 A>1 0 (10)^a 1 1 0 (10)^(c+1)` becomes `1 A>1 0 (10)^(a+2) 0 (10)^(c+1)` (written as the run leaves it). -/
theorem bounce1_cells (a c : Nat) (R : Tape) :
    steps (4 * a + 10) ⟨cons true (blank), cons true (cons false (rep (a) [true, false] (cons true (cons true (cons false (rep (c + 1) [true, false] (R))))))), .A⟩ = some ⟨cons true (blank), cons true (cons false (cons true (cons false (cons true (rep (a) [false, true] (cons false (cons false (rep (c + 1) [true, false] (R))))))))), .A⟩ := by
  have h0 : steps 2 ⟨cons true (blank), cons true (cons false (rep (a) [true, false] (cons true (cons true (cons false (rep (c + 1) [true, false] (R))))))), .A⟩ = some ⟨cons true (cons false (cons true (blank))), rep (a) [true, false] (cons true (cons true (cons false (rep (c + 1) [true, false] (R))))), .A⟩ := rfl
  have c1 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, false] R, .A⟩ = some ⟨app [] (app [true, false] L), R, .A⟩ := fun _ _ => rfl
  have h1 : steps ((a) * 2) ⟨cons true (cons false (cons true (blank))), rep (a) [true, false] (cons true (cons true (cons false (rep (c + 1) [true, false] (R))))), .A⟩ = some ⟨rep (a) [true, false] (cons true (cons false (cons true (blank)))), cons true (cons true (cons false (rep (c + 1) [true, false] (R)))), .A⟩ :=
    cross_r trans c1 (a) (cons true (cons false (cons true (blank)))) (cons true (cons true (cons false (rep (c + 1) [true, false] (R)))))
  have h2 : steps 2 ⟨rep (a) [true, false] (cons true (cons false (cons true (blank)))), cons true (cons true (cons false (rep (c + 1) [true, false] (R)))), .A⟩ = some ⟨rep (a) [true, false] (cons true (cons false (cons true (blank)))), cons false (cons false (cons false (rep (c + 1) [true, false] (R)))), .B⟩ := rfl
  have c3 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .B⟩ = some ⟨L, app [false] (app [false, true] R), .B⟩ := fun _ _ => rfl
  have h3 : steps ((a) * 2) ⟨rep (a) [true, false] (cons true (cons false (cons true (blank)))), cons false (cons false (cons false (rep (c + 1) [true, false] (R)))), .B⟩ = some ⟨cons true (cons false (cons true (blank))), cons false (rep (a) [false, true] (cons false (cons false (rep (c + 1) [true, false] (R))))), .B⟩ :=
    cross_l trans c3 (a) (cons true (cons false (cons true (blank)))) (cons false (cons false (rep (c + 1) [true, false] (R))))
  have h4 : steps 6 ⟨cons true (cons false (cons true (blank))), cons false (rep (a) [false, true] (cons false (cons false (rep (c + 1) [true, false] (R))))), .B⟩ = some ⟨cons true (blank), cons true (cons false (cons true (cons false (cons true (rep (a) [false, true] (cons false (cons false (rep (c + 1) [true, false] (R))))))))), .A⟩ := rfl
  exact steps_congr trans (a := 2 + ((a) * 2 + (2 + ((a) * 2 + (6))))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

end H54407
