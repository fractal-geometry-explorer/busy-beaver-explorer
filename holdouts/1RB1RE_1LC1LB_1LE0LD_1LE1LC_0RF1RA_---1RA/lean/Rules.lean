import Machine

/-! Writes lean/Rules.lean: the two proved moves of 1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA at the left end. Written by `py/rules.py` with `bbtools.symtm.prove`; checked by the kernel. -/

namespace H175628

open TM

/-- One sweep: the long run at the left grows by 6 and the unit block loses two units. -/
theorem sweep (n x : Nat) (R : Tape) :
    steps (4 * x + 36) ⟨blank, cons false (rep (x + 1) [true, true] (cons false (cons true (cons true (cons true (cons true (cons false (rep (n + 2) [true, false] (R))))))))), .B⟩ = some ⟨blank, cons false (cons true (cons true (cons true (rep (x) [true, true] (cons true (cons true (cons true (cons true (cons true (cons false (cons true (cons true (cons true (cons true (cons false (rep (n) [true, false] (R))))))))))))))))), .B⟩ := by
  have h0 : steps 5 ⟨blank, cons false (rep (x + 1) [true, true] (cons false (cons true (cons true (cons true (cons true (cons false (rep (n + 2) [true, false] (R))))))))), .B⟩ = some ⟨cons true (cons true (cons false (blank))), rep (x + 1) [true, true] (cons false (cons true (cons true (cons true (cons true (cons false (rep (n + 2) [true, false] (R)))))))), .E⟩ := rfl
  have c1 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, true] R, .E⟩ = some ⟨app [] (app [true, true] L), R, .E⟩ := fun _ _ => rfl
  have h1 : steps ((x + 1) * 2) ⟨cons true (cons true (cons false (blank))), rep (x + 1) [true, true] (cons false (cons true (cons true (cons true (cons true (cons false (rep (n + 2) [true, false] (R)))))))), .E⟩ = some ⟨rep (x + 1) [true, true] (cons true (cons true (cons false (blank)))), cons false (cons true (cons true (cons true (cons true (cons false (rep (n + 2) [true, false] (R))))))), .E⟩ :=
    cross_r trans c1 (x + 1) (cons true (cons true (cons false (blank)))) (cons false (cons true (cons true (cons true (cons true (cons false (rep (n + 2) [true, false] (R))))))))
  have h2 : steps 26 ⟨rep (x + 1) [true, true] (cons true (cons true (cons false (blank)))), cons false (cons true (cons true (cons true (cons true (cons false (rep (n + 2) [true, false] (R))))))), .E⟩ = some ⟨rep (x) [true, true] (cons true (cons true (cons false (blank)))), cons true (cons true (cons true (cons true (cons true (cons true (cons false (cons true (cons true (cons true (cons true (cons false (rep (n) [true, false] (R))))))))))))), .B⟩ := rfl
  have c3 : ∀ L R : Tape, steps 2 ⟨app [true, true] L, app [true] R, .B⟩ = some ⟨L, app [true] (app [true, true] R), .B⟩ := fun _ _ => rfl
  have h3 : steps ((x) * 2) ⟨rep (x) [true, true] (cons true (cons true (cons false (blank)))), cons true (cons true (cons true (cons true (cons true (cons true (cons false (cons true (cons true (cons true (cons true (cons false (rep (n) [true, false] (R))))))))))))), .B⟩ = some ⟨cons true (cons true (cons false (blank))), cons true (rep (x) [true, true] (cons true (cons true (cons true (cons true (cons true (cons false (cons true (cons true (cons true (cons true (cons false (rep (n) [true, false] (R)))))))))))))), .B⟩ :=
    cross_l trans c3 (x) (cons true (cons true (cons false (blank)))) (cons true (cons true (cons true (cons true (cons true (cons false (cons true (cons true (cons true (cons true (cons false (rep (n) [true, false] (R)))))))))))))
  have h4 : steps 3 ⟨cons true (cons true (cons false (blank))), cons true (rep (x) [true, true] (cons true (cons true (cons true (cons true (cons true (cons false (cons true (cons true (cons true (cons true (cons false (rep (n) [true, false] (R)))))))))))))), .B⟩ = some ⟨blank, cons false (cons true (cons true (cons true (rep (x) [true, true] (cons true (cons true (cons true (cons true (cons true (cons false (cons true (cons true (cons true (cons true (cons false (rep (n) [true, false] (R))))))))))))))))), .B⟩ := rfl
  exact steps_congr trans (a := 5 + ((x + 1) * 2 + (26 + ((x) * 2 + (3))))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

/-- The end of an epoch: a run of 2x+8 ones becomes x units (after a new 6 and 4), and two units of the next block become a 4. -/
theorem convert (k x : Nat) (R : Tape) :
    steps (4 * x + 74) ⟨blank, cons false (rep (x + 4) [true, true] (cons false (rep (k + 2) [true, false] (R)))), .B⟩ = some ⟨blank, cons false (cons true (cons true (cons true (cons true (cons true (cons true (cons false (cons true (cons true (cons true (cons true (rep (x) [false, true] (cons false (cons true (cons true (cons true (cons true (cons false (rep (k) [true, false] (R)))))))))))))))))))), .B⟩ := by
  have h0 : steps 5 ⟨blank, cons false (rep (x + 4) [true, true] (cons false (rep (k + 2) [true, false] (R)))), .B⟩ = some ⟨cons true (cons true (cons false (blank))), rep (x + 4) [true, true] (cons false (rep (k + 2) [true, false] (R))), .E⟩ := rfl
  have c1 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, true] R, .E⟩ = some ⟨app [] (app [true, true] L), R, .E⟩ := fun _ _ => rfl
  have h1 : steps ((x + 4) * 2) ⟨cons true (cons true (cons false (blank))), rep (x + 4) [true, true] (cons false (rep (k + 2) [true, false] (R))), .E⟩ = some ⟨rep (x + 4) [true, true] (cons true (cons true (cons false (blank)))), cons false (rep (k + 2) [true, false] (R)), .E⟩ :=
    cross_r trans c1 (x + 4) (cons true (cons true (cons false (blank)))) (cons false (rep (k + 2) [true, false] (R)))
  have h2 : steps 8 ⟨rep (x + 4) [true, true] (cons true (cons true (cons false (blank)))), cons false (rep (k + 2) [true, false] (R)), .E⟩ = some ⟨rep (x + 3) [true, true] (cons true (cons true (cons false (blank)))), cons true (cons false (cons true (cons true (cons true (cons true (cons false (rep (k) [true, false] (R)))))))), .D⟩ := rfl
  have c3 : ∀ L R : Tape, steps 2 ⟨app [true, true] L, app [true] R, .D⟩ = some ⟨L, app [true] (app [false, true] R), .D⟩ := fun _ _ => rfl
  have h3 : steps ((x + 3) * 2) ⟨rep (x + 3) [true, true] (cons true (cons true (cons false (blank)))), cons true (cons false (cons true (cons true (cons true (cons true (cons false (rep (k) [true, false] (R)))))))), .D⟩ = some ⟨cons true (cons true (cons false (blank))), cons true (rep (x + 3) [false, true] (cons false (cons true (cons true (cons true (cons true (cons false (rep (k) [true, false] (R))))))))), .D⟩ :=
    cross_l trans c3 (x + 3) (cons true (cons true (cons false (blank)))) (cons false (cons true (cons true (cons true (cons true (cons false (rep (k) [true, false] (R))))))))
  have h4 : steps 47 ⟨cons true (cons true (cons false (blank))), cons true (rep (x + 3) [false, true] (cons false (cons true (cons true (cons true (cons true (cons false (rep (k) [true, false] (R))))))))), .D⟩ = some ⟨blank, cons false (cons true (cons true (cons true (cons true (cons true (cons true (cons false (cons true (cons true (cons true (cons true (rep (x) [false, true] (cons false (cons true (cons true (cons true (cons true (cons false (rep (k) [true, false] (R)))))))))))))))))))), .B⟩ := rfl
  exact steps_congr trans (a := 5 + ((x + 4) * 2 + (8 + ((x + 3) * 2 + (47))))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

end H175628
