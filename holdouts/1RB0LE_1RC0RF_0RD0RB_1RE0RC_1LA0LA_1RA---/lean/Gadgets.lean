import Machine

/-! The fill sweep of 1RB0LE_1RC0RF_0RD0RB_1RE0RC_1LA0LA_1RA---, written by `py/gen_gadgets.py` (bbtools.symtm.prove). -/

namespace H70977

open TM

/-- One fill sweep, with the end written as the run reaches it. -/
theorem fill_raw (m z : Nat) (L : Tape) :
    steps (4 * m + 40) ⟨cons true (rep (m) [false, true] (cons false (cons true (cons true (cons true (cons false (cons true (rep (z + 4) [false] (L))))))))), blank, .E⟩ = some ⟨cons true (cons false (cons true (cons false (rep (m) [true, false] (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons true (cons false (cons true (rep (z) [false] (L))))))))))))))))), blank, .E⟩ := by
  have h0 : steps 1 ⟨cons true (rep (m) [false, true] (cons false (cons true (cons true (cons true (cons false (cons true (rep (z + 4) [false] (L))))))))), blank, .E⟩ = some ⟨rep (m) [false, true] (cons false (cons true (cons true (cons true (cons false (cons true (rep (z + 4) [false] (L)))))))), cons true (cons true (blank)), .A⟩ := rfl
  have c1 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false] R), .A⟩ := fun _ _ => rfl
  have h1 : steps ((m) * 2) ⟨rep (m) [false, true] (cons false (cons true (cons true (cons true (cons false (cons true (rep (z + 4) [false] (L)))))))), cons true (cons true (blank)), .A⟩ = some ⟨cons false (cons true (cons true (cons true (cons false (cons true (rep (z + 4) [false] (L))))))), cons true (rep (m) [true, false] (cons true (blank))), .A⟩ :=
    cross_l trans c1 (m) (cons false (cons true (cons true (cons true (cons false (cons true (rep (z + 4) [false] (L)))))))) (cons true (blank))
  have h2 : steps 35 ⟨cons false (cons true (cons true (cons true (cons false (cons true (rep (z + 4) [false] (L))))))), cons true (rep (m) [true, false] (cons true (blank))), .A⟩ = some ⟨cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons true (cons false (cons true (rep (z) [false] (L)))))))))))), rep (m) [true, false] (cons true (blank)), .C⟩ := rfl
  have c3 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, false] R, .C⟩ = some ⟨app [] (app [true, false] L), R, .C⟩ := fun _ _ => rfl
  have h3 : steps ((m) * 2) ⟨cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons true (cons false (cons true (rep (z) [false] (L)))))))))))), rep (m) [true, false] (cons true (blank)), .C⟩ = some ⟨rep (m) [true, false] (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons true (cons false (cons true (rep (z) [false] (L))))))))))))), cons true (blank), .C⟩ :=
    cross_r trans c3 (m) (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons true (cons false (cons true (rep (z) [false] (L))))))))))))) (cons true (blank))
  have h4 : steps 4 ⟨rep (m) [true, false] (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons true (cons false (cons true (rep (z) [false] (L))))))))))))), cons true (blank), .C⟩ = some ⟨cons true (cons false (cons true (cons false (rep (m) [true, false] (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons true (cons false (cons true (rep (z) [false] (L))))))))))))))))), blank, .E⟩ := rfl
  exact steps_congr trans (a := 1 + ((m) * 2 + (35 + ((m) * 2 + (4))))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

end H70977
