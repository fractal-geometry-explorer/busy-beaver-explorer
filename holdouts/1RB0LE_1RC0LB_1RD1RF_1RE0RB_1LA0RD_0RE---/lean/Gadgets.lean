import Machine

/-! Cell-level gadgets of 1RB0LE_1RC0LB_1RD1RF_1RE0RB_1LA0RD_0RE---, written by `py/gen_gadgets.py` (bbtools.symtm.prove). -/

namespace H3006

open TM

/-- The S-gadget: the leftward signal crosses a separator `01100`, which becomes `(10)^2 1` on its right. -/
theorem sgad (L R : Tape) :
    steps (21) ⟨cons false (cons false (cons true (cons true (cons false (L))))), cons true (R), .A⟩ = some ⟨L, cons true (cons true (cons false (cons true (cons false (cons true (R)))))), .A⟩ := by
  have h0 : steps 21 ⟨cons false (cons false (cons true (cons true (cons false (L))))), cons true (R), .A⟩ = some ⟨L, cons true (cons true (cons false (cons true (cons false (cons true (R)))))), .A⟩ := rfl
  exact steps_congr trans (a := 21) (by omega) (h0)

/-- The turn at a defect `1`: it becomes `0`, the first right block grows by one and `D` starts right. -/
theorem turn1 (Y : Nat) (L R : Tape) :
    steps (2 * Y + 4) ⟨cons true (L), cons true (rep (Y) [true, false] (cons true (R))), .A⟩ = some ⟨cons false (rep (Y) [true, false] (cons true (cons false (L)))), R, .D⟩ := by
  have h0 : steps 3 ⟨cons true (L), cons true (rep (Y) [true, false] (cons true (R))), .A⟩ = some ⟨cons true (cons false (L)), rep (Y) [true, false] (cons true (R)), .E⟩ := rfl
  have c1 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, false] R, .E⟩ = some ⟨app [] (app [true, false] L), R, .E⟩ := fun _ _ => rfl
  have h1 : steps ((Y) * 2) ⟨cons true (cons false (L)), rep (Y) [true, false] (cons true (R)), .E⟩ = some ⟨rep (Y) [true, false] (cons true (cons false (L))), cons true (R), .E⟩ :=
    cross_r trans c1 (Y) (cons true (cons false (L))) (cons true (R))
  have h2 : steps 1 ⟨rep (Y) [true, false] (cons true (cons false (L))), cons true (R), .E⟩ = some ⟨cons false (rep (Y) [true, false] (cons true (cons false (L)))), R, .D⟩ := rfl
  exact steps_congr trans (a := 3 + ((Y) * 2 + (1))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (h2)))

/-- The turn at a defect `0` with a block of at least 2 before it. -/
theorem turn0 (Y x : Nat) (L R : Tape) :
    steps (2 * Y + 16) ⟨cons false (rep (x + 2) [false, true] (L)), cons true (rep (Y) [true, false] (cons true (R))), .A⟩ = some ⟨cons false (rep (Y) [true, false] (cons true (cons false (cons true (cons false (cons true (cons true (rep (x) [false, true] (L))))))))), R, .D⟩ := by
  have h0 : steps 15 ⟨cons false (rep (x + 2) [false, true] (L)), cons true (rep (Y) [true, false] (cons true (R))), .A⟩ = some ⟨cons true (cons false (cons true (cons false (cons true (cons true (rep (x) [false, true] (L))))))), rep (Y) [true, false] (cons true (R)), .E⟩ := rfl
  have c1 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, false] R, .E⟩ = some ⟨app [] (app [true, false] L), R, .E⟩ := fun _ _ => rfl
  have h1 : steps ((Y) * 2) ⟨cons true (cons false (cons true (cons false (cons true (cons true (rep (x) [false, true] (L))))))), rep (Y) [true, false] (cons true (R)), .E⟩ = some ⟨rep (Y) [true, false] (cons true (cons false (cons true (cons false (cons true (cons true (rep (x) [false, true] (L)))))))), cons true (R), .E⟩ :=
    cross_r trans c1 (Y) (cons true (cons false (cons true (cons false (cons true (cons true (rep (x) [false, true] (L)))))))) (cons true (R))
  have h2 : steps 1 ⟨rep (Y) [true, false] (cons true (cons false (cons true (cons false (cons true (cons true (rep (x) [false, true] (L)))))))), cons true (R), .E⟩ = some ⟨cons false (rep (Y) [true, false] (cons true (cons false (cons true (cons false (cons true (cons true (rep (x) [false, true] (L))))))))), R, .D⟩ := rfl
  exact steps_congr trans (a := 15 + ((Y) * 2 + (1))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (h2)))

/-- The rightward `D` unit: `(10)^(s+2) 1` becomes a separator and `(10)^s`. -/
theorem dunit (s : Nat) (L R : Tape) :
    steps (2 * s + 5) ⟨L, rep (s + 2) [true, false] (cons true (R)), .D⟩ = some ⟨cons false (rep (s) [true, false] (cons false (cons true (cons true (cons false (L)))))), R, .D⟩ := by
  have h0 : steps 4 ⟨L, rep (s + 2) [true, false] (cons true (R)), .D⟩ = some ⟨cons false (cons true (cons true (cons false (L)))), rep (s) [true, false] (cons true (R)), .E⟩ := rfl
  have c1 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, false] R, .E⟩ = some ⟨app [] (app [true, false] L), R, .E⟩ := fun _ _ => rfl
  have h1 : steps ((s) * 2) ⟨cons false (cons true (cons true (cons false (L)))), rep (s) [true, false] (cons true (R)), .E⟩ = some ⟨rep (s) [true, false] (cons false (cons true (cons true (cons false (L))))), cons true (R), .E⟩ :=
    cross_r trans c1 (s) (cons false (cons true (cons true (cons false (L))))) (cons true (R))
  have h2 : steps 1 ⟨rep (s) [true, false] (cons false (cons true (cons true (cons false (L))))), cons true (R), .E⟩ = some ⟨cons false (rep (s) [true, false] (cons false (cons true (cons true (cons false (L)))))), R, .D⟩ := rfl
  exact steps_congr trans (a := 4 + ((s) * 2 + (1))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (h2)))

end H3006
