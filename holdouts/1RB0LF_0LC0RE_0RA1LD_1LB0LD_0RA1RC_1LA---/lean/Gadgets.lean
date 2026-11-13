import Machine

/-! Gadgets of 1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA---, written by `py/gen_gadgets.py` (bbtools.symtm.prove). -/

namespace H129771

open TM

/-- The short sweep at the left end, `1 0^3` after the first block becoming `1^2 0 1^2 0`, as the run writes it. -/
theorem short_raw (x : Nat) (R : Tape) :
    steps (12 * x + 36) ⟨blank, cons false (rep (x + 2) [true, false, true, false] (cons true (cons false (cons false (cons false (R)))))), .B⟩ = some ⟨blank, cons false (cons true (cons false (cons true (rep (x + 1) [false, true, false, true] (cons false (cons true (cons true (cons false (cons true (cons true (cons false (R)))))))))))), .B⟩ := by
  have h0 : steps 3 ⟨blank, cons false (rep (x + 2) [true, false, true, false] (cons true (cons false (cons false (cons false (R)))))), .B⟩ = some ⟨cons true (cons false (blank)), rep (x + 2) [true, false, true, false] (cons true (cons false (cons false (cons false (R))))), .B⟩ := rfl
  have c1 : ∀ L R : Tape, steps 8 ⟨app [] L, app [true, false, true, false] R, .B⟩ = some ⟨app [] (app [true, false, false, true] L), R, .B⟩ := fun _ _ => rfl
  have h1 : steps ((x + 2) * 8) ⟨cons true (cons false (blank)), rep (x + 2) [true, false, true, false] (cons true (cons false (cons false (cons false (R))))), .B⟩ = some ⟨rep (x + 2) [true, false, false, true] (cons true (cons false (blank))), cons true (cons false (cons false (cons false (R)))), .B⟩ :=
    cross_r trans c1 (x + 2) (cons true (cons false (blank))) (cons true (cons false (cons false (cons false (R)))))
  have h2 : steps 10 ⟨rep (x + 2) [true, false, false, true] (cons true (cons false (blank))), cons true (cons false (cons false (cons false (R)))), .B⟩ = some ⟨rep (x + 1) [true, false, false, true] (cons true (cons false (blank))), cons true (cons false (cons true (cons true (cons false (cons true (cons true (cons false (R)))))))), .C⟩ := rfl
  have c3 : ∀ L R : Tape, steps 4 ⟨app [true, false, false, true] L, app [true] R, .C⟩ = some ⟨L, app [true] (app [false, true, false, true] R), .C⟩ := fun _ _ => rfl
  have h3 : steps ((x + 1) * 4) ⟨rep (x + 1) [true, false, false, true] (cons true (cons false (blank))), cons true (cons false (cons true (cons true (cons false (cons true (cons true (cons false (R)))))))), .C⟩ = some ⟨cons true (cons false (blank)), cons true (rep (x + 1) [false, true, false, true] (cons false (cons true (cons true (cons false (cons true (cons true (cons false (R))))))))), .C⟩ :=
    cross_l trans c3 (x + 1) (cons true (cons false (blank))) (cons false (cons true (cons true (cons false (cons true (cons true (cons false (R))))))))
  have h4 : steps 3 ⟨cons true (cons false (blank)), cons true (rep (x + 1) [false, true, false, true] (cons false (cons true (cons true (cons false (cons true (cons true (cons false (R))))))))), .C⟩ = some ⟨blank, cons false (cons true (cons false (cons true (rep (x + 1) [false, true, false, true] (cons false (cons true (cons true (cons false (cons true (cons true (cons false (R)))))))))))), .B⟩ := rfl
  exact steps_congr trans (a := 3 + ((x + 2) * 8 + (10 + ((x + 1) * 4 + (3))))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

end H129771
