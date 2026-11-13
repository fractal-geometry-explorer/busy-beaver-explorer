import Machine

/-! The two local rules of the tick, written by `bbtools.symtm.prove` (from `holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/gen_clock.py`). -/

namespace H38215

open TM

/-- The sweep: `0 0 0 E> 1^(4+3n) 0` becomes `1 1 1 0^(3+3n) 1 1 A>`. -/
theorem rule_sweep (n : Nat) (L R : Tape) :
    steps (3 * n + 13) ⟨cons false (cons false (cons false (L))), cons true (rep (3 * n) [true] (cons true (cons true (cons true (cons false (R)))))), .E⟩ = some ⟨cons true (cons true (cons false (cons false (rep (3 * n) [false] (cons false (cons true (cons true (cons true (L))))))))), R, .A⟩ := by
  have h0 : steps 7 ⟨cons false (cons false (cons false (L))), cons true (rep (3 * n) [true] (cons true (cons true (cons true (cons false (R)))))), .E⟩ = some ⟨cons false (cons true (cons true (cons true (L)))), rep (3 * n) [true] (cons true (cons true (cons true (cons false (R))))), .B⟩ := rfl
  have c1 : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .B⟩ = some ⟨app [] (app [false] L), R, .B⟩ := fun _ _ => rfl
  have h1 : steps ((3 * n) * 1) ⟨cons false (cons true (cons true (cons true (L)))), rep (3 * n) [true] (cons true (cons true (cons true (cons false (R))))), .B⟩ = some ⟨rep (3 * n) [false] (cons false (cons true (cons true (cons true (L))))), cons true (cons true (cons true (cons false (R)))), .B⟩ :=
    cross_r trans c1 (3 * n) (cons false (cons true (cons true (cons true (L))))) (cons true (cons true (cons true (cons false (R)))))
  have h2 : steps 6 ⟨rep (3 * n) [false] (cons false (cons true (cons true (cons true (L))))), cons true (cons true (cons true (cons false (R)))), .B⟩ = some ⟨cons true (cons true (cons false (cons false (rep (3 * n) [false] (cons false (cons true (cons true (cons true (L))))))))), R, .A⟩ := rfl
  exact steps_congr trans (a := 7 + ((3 * n) * 1 + (6))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (h2)))

/-- The merge: `1 1 1 E> 1` becomes `E> 1 1 1 1`. -/
theorem rule_merge (L R : Tape) :
    steps (3) ⟨cons true (cons true (cons true (L))), cons true (R), .E⟩ = some ⟨L, cons true (cons true (cons true (cons true (R)))), .E⟩ := by
  have h0 : steps 3 ⟨cons true (cons true (cons true (L))), cons true (R), .E⟩ = some ⟨L, cons true (cons true (cons true (cons true (R)))), .E⟩ := rfl
  exact steps_congr trans (a := 3) (by omega) (h0)

end H38215
