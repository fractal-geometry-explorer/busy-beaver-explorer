import Machine

/-! # 1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB: the rules of the drain machine

Each rule holds for every count and every tape in the contexts L, R; written by `py/macro_rules.py` with `bbtools.symtm` (a symbolic run, its trace checked by the kernel).  `0^inf` is blank tape: those rules use the left end of the tape. -/

namespace H8002

open TM

/-- Drain sweep D(A+3,B) -> D(A+1,B+2): the head goes left over the pairs to the block of 1s and back; two 1s become a pair `01` and the head moves two cells right.  It reads only one cell past the head, so the rest R is any tape. -/
theorem m_sweep (b : Nat) (L R : Tape) :
    steps (6 * b + 16) ⟨cons false (rep (b) [true, false] (cons true (cons true (cons true (L))))), cons false (cons false (R)), .C⟩ = some ⟨cons false (cons true (rep (b) [false, true] (cons false (cons true (cons false (cons true (L))))))), R, .C⟩ := by
  have hn : 2 + (0 + ((b) * 2 + (10 + (0 + ((b) * 4 + (4)))))) = 6 * b + 16 := by omega
  have h0 : steps 2 ⟨cons false (rep (b) [true, false] (cons true (cons true (cons true (L))))), cons false (cons false (R)), .C⟩ = some ⟨cons false (rep (b) [true, false] (cons true (cons true (cons true (L))))), cons true (cons true (R)), .E⟩ := rfl
  have h1 : steps 0 ⟨cons false (rep (b) [true, false] (cons true (cons true (cons true (L))))), cons true (cons true (R)), .E⟩ = some ⟨rep (b) [false, true] (cons false (cons true (cons true (cons true (L))))), cons true (cons true (R)), .E⟩ := by
    simp only [steps_zero, show cons false (rep (b) [true, false] (cons true (cons true (cons true (L))))) = rep (b) [false, true] (cons false (cons true (cons true (cons true (L))))) from
      rep_rotate (b) [false] [true, false] [false, true] rfl (cons true (cons true (cons true (L))))]
  have c2 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .E⟩ = some ⟨L, app [true] (app [true, false] R), .E⟩ := fun _ _ => rfl
  have h2 : steps ((b) * 2) ⟨rep (b) [false, true] (cons false (cons true (cons true (cons true (L))))), cons true (cons true (R)), .E⟩ = some ⟨cons false (cons true (cons true (cons true (L)))), cons true (rep (b) [true, false] (cons true (R))), .E⟩ :=
    cross_l trans c2 (b) (cons false (cons true (cons true (cons true (L))))) (cons true (R))
  have h3 : steps 10 ⟨cons false (cons true (cons true (cons true (L)))), cons true (rep (b) [true, false] (cons true (R))), .E⟩ = some ⟨cons false (cons true (cons false (cons true (L)))), cons false (rep (b) [true, false] (cons true (R))), .C⟩ := rfl
  have h4 : steps 0 ⟨cons false (cons true (cons false (cons true (L)))), cons false (rep (b) [true, false] (cons true (R))), .C⟩ = some ⟨cons false (cons true (cons false (cons true (L)))), rep (b) [false, true] (cons false (cons true (R))), .C⟩ := by
    simp only [steps_zero, show cons false (rep (b) [true, false] (cons true (R))) = rep (b) [false, true] (cons false (cons true (R))) from
      rep_rotate (b) [false] [true, false] [false, true] rfl (cons true (R))]
  have c5 : ∀ L R : Tape, steps 4 ⟨app [] L, app [false, true] R, .C⟩ = some ⟨app [] (app [false, true] L), R, .C⟩ := fun _ _ => rfl
  have h5 : steps ((b) * 4) ⟨cons false (cons true (cons false (cons true (L)))), rep (b) [false, true] (cons false (cons true (R))), .C⟩ = some ⟨rep (b) [false, true] (cons false (cons true (cons false (cons true (L))))), cons false (cons true (R)), .C⟩ :=
    cross_r trans c5 (b) (cons false (cons true (cons false (cons true (L))))) (cons false (cons true (R)))
  have h6 : steps 4 ⟨rep (b) [false, true] (cons false (cons true (cons false (cons true (L))))), cons false (cons true (R)), .C⟩ = some ⟨cons false (cons true (rep (b) [false, true] (cons false (cons true (cons false (cons true (L))))))), R, .C⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (steps_seq trans h5 (h6)))))))

/-- Odd sweep, the drain next to a block `0 (10)^(c+2) 1` (a gap of one 0): D(A+3,B) -> D(A+1,B+3) and the block loses two pairs.  This is the round of the ternary step. -/
theorem m_odd (b c : Nat) (L R : Tape) :
    steps (6 * b + 24) ⟨cons false (rep (b) [true, false] (cons true (cons true (cons true (L))))), cons false (cons false (rep (c + 2) [true, false] (cons true (R)))), .C⟩ = some ⟨cons false (cons true (cons false (cons true (rep (b) [false, true] (cons false (cons true (cons false (cons true (L))))))))), cons false (cons false (rep (c) [true, false] (cons true (R)))), .C⟩ := by
  have hn : 2 + (0 + ((b) * 2 + (10 + (0 + ((b) * 4 + (12)))))) = 6 * b + 24 := by omega
  have h0 : steps 2 ⟨cons false (rep (b) [true, false] (cons true (cons true (cons true (L))))), cons false (cons false (rep (c + 2) [true, false] (cons true (R)))), .C⟩ = some ⟨cons false (rep (b) [true, false] (cons true (cons true (cons true (L))))), cons true (cons true (rep (c + 2) [true, false] (cons true (R)))), .E⟩ := rfl
  have h1 : steps 0 ⟨cons false (rep (b) [true, false] (cons true (cons true (cons true (L))))), cons true (cons true (rep (c + 2) [true, false] (cons true (R)))), .E⟩ = some ⟨rep (b) [false, true] (cons false (cons true (cons true (cons true (L))))), cons true (cons true (rep (c + 2) [true, false] (cons true (R)))), .E⟩ := by
    simp only [steps_zero, show cons false (rep (b) [true, false] (cons true (cons true (cons true (L))))) = rep (b) [false, true] (cons false (cons true (cons true (cons true (L))))) from
      rep_rotate (b) [false] [true, false] [false, true] rfl (cons true (cons true (cons true (L))))]
  have c2 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .E⟩ = some ⟨L, app [true] (app [true, false] R), .E⟩ := fun _ _ => rfl
  have h2 : steps ((b) * 2) ⟨rep (b) [false, true] (cons false (cons true (cons true (cons true (L))))), cons true (cons true (rep (c + 2) [true, false] (cons true (R)))), .E⟩ = some ⟨cons false (cons true (cons true (cons true (L)))), cons true (rep (b) [true, false] (cons true (rep (c + 2) [true, false] (cons true (R))))), .E⟩ :=
    cross_l trans c2 (b) (cons false (cons true (cons true (cons true (L))))) (cons true (rep (c + 2) [true, false] (cons true (R))))
  have h3 : steps 10 ⟨cons false (cons true (cons true (cons true (L)))), cons true (rep (b) [true, false] (cons true (rep (c + 2) [true, false] (cons true (R))))), .E⟩ = some ⟨cons false (cons true (cons false (cons true (L)))), cons false (rep (b) [true, false] (cons true (rep (c + 2) [true, false] (cons true (R))))), .C⟩ := rfl
  have h4 : steps 0 ⟨cons false (cons true (cons false (cons true (L)))), cons false (rep (b) [true, false] (cons true (rep (c + 2) [true, false] (cons true (R))))), .C⟩ = some ⟨cons false (cons true (cons false (cons true (L)))), rep (b) [false, true] (cons false (cons true (rep (c + 2) [true, false] (cons true (R))))), .C⟩ := by
    simp only [steps_zero, show cons false (rep (b) [true, false] (cons true (rep (c + 2) [true, false] (cons true (R))))) = rep (b) [false, true] (cons false (cons true (rep (c + 2) [true, false] (cons true (R))))) from
      rep_rotate (b) [false] [true, false] [false, true] rfl (cons true (rep (c + 2) [true, false] (cons true (R))))]
  have c5 : ∀ L R : Tape, steps 4 ⟨app [] L, app [false, true] R, .C⟩ = some ⟨app [] (app [false, true] L), R, .C⟩ := fun _ _ => rfl
  have h5 : steps ((b) * 4) ⟨cons false (cons true (cons false (cons true (L)))), rep (b) [false, true] (cons false (cons true (rep (c + 2) [true, false] (cons true (R))))), .C⟩ = some ⟨rep (b) [false, true] (cons false (cons true (cons false (cons true (L))))), cons false (cons true (rep (c + 2) [true, false] (cons true (R)))), .C⟩ :=
    cross_r trans c5 (b) (cons false (cons true (cons false (cons true (L))))) (cons false (cons true (rep (c + 2) [true, false] (cons true (R)))))
  have h6 : steps 12 ⟨rep (b) [false, true] (cons false (cons true (cons false (cons true (L))))), cons false (cons true (rep (c + 2) [true, false] (cons true (R)))), .C⟩ = some ⟨cons false (cons true (cons false (cons true (rep (b) [false, true] (cons false (cons true (cons false (cons true (L))))))))), cons false (cons false (rep (c) [true, false] (cons true (R)))), .C⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (steps_seq trans h5 (h6)))))))

/-- The odd sweep at the last pair of its block: `0 (10) 1` is used up, D(A+3,B) -> D(A+1,B+3). -/
theorem m_odd_end1 (b : Nat) (L R : Tape) :
    steps (6 * b + 24) ⟨cons false (rep (b) [true, false] (cons true (cons true (cons true (L))))), cons false (cons false (cons true (cons false (cons true (cons false (R)))))), .C⟩ = some ⟨cons false (cons true (cons false (cons true (rep (b) [false, true] (cons false (cons true (cons false (cons true (L))))))))), cons false (cons false (R)), .C⟩ := by
  have hn : 2 + (0 + ((b) * 2 + (10 + (0 + ((b) * 4 + (12)))))) = 6 * b + 24 := by omega
  have h0 : steps 2 ⟨cons false (rep (b) [true, false] (cons true (cons true (cons true (L))))), cons false (cons false (cons true (cons false (cons true (cons false (R)))))), .C⟩ = some ⟨cons false (rep (b) [true, false] (cons true (cons true (cons true (L))))), cons true (cons true (cons true (cons false (cons true (cons false (R)))))), .E⟩ := rfl
  have h1 : steps 0 ⟨cons false (rep (b) [true, false] (cons true (cons true (cons true (L))))), cons true (cons true (cons true (cons false (cons true (cons false (R)))))), .E⟩ = some ⟨rep (b) [false, true] (cons false (cons true (cons true (cons true (L))))), cons true (cons true (cons true (cons false (cons true (cons false (R)))))), .E⟩ := by
    simp only [steps_zero, show cons false (rep (b) [true, false] (cons true (cons true (cons true (L))))) = rep (b) [false, true] (cons false (cons true (cons true (cons true (L))))) from
      rep_rotate (b) [false] [true, false] [false, true] rfl (cons true (cons true (cons true (L))))]
  have c2 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .E⟩ = some ⟨L, app [true] (app [true, false] R), .E⟩ := fun _ _ => rfl
  have h2 : steps ((b) * 2) ⟨rep (b) [false, true] (cons false (cons true (cons true (cons true (L))))), cons true (cons true (cons true (cons false (cons true (cons false (R)))))), .E⟩ = some ⟨cons false (cons true (cons true (cons true (L)))), cons true (rep (b) [true, false] (cons true (cons true (cons false (cons true (cons false (R))))))), .E⟩ :=
    cross_l trans c2 (b) (cons false (cons true (cons true (cons true (L))))) (cons true (cons true (cons false (cons true (cons false (R))))))
  have h3 : steps 10 ⟨cons false (cons true (cons true (cons true (L)))), cons true (rep (b) [true, false] (cons true (cons true (cons false (cons true (cons false (R))))))), .E⟩ = some ⟨cons false (cons true (cons false (cons true (L)))), cons false (rep (b) [true, false] (cons true (cons true (cons false (cons true (cons false (R))))))), .C⟩ := rfl
  have h4 : steps 0 ⟨cons false (cons true (cons false (cons true (L)))), cons false (rep (b) [true, false] (cons true (cons true (cons false (cons true (cons false (R))))))), .C⟩ = some ⟨cons false (cons true (cons false (cons true (L)))), rep (b) [false, true] (cons false (cons true (cons true (cons false (cons true (cons false (R))))))), .C⟩ := by
    simp only [steps_zero, show cons false (rep (b) [true, false] (cons true (cons true (cons false (cons true (cons false (R))))))) = rep (b) [false, true] (cons false (cons true (cons true (cons false (cons true (cons false (R))))))) from
      rep_rotate (b) [false] [true, false] [false, true] rfl (cons true (cons true (cons false (cons true (cons false (R))))))]
  have c5 : ∀ L R : Tape, steps 4 ⟨app [] L, app [false, true] R, .C⟩ = some ⟨app [] (app [false, true] L), R, .C⟩ := fun _ _ => rfl
  have h5 : steps ((b) * 4) ⟨cons false (cons true (cons false (cons true (L)))), rep (b) [false, true] (cons false (cons true (cons true (cons false (cons true (cons false (R))))))), .C⟩ = some ⟨rep (b) [false, true] (cons false (cons true (cons false (cons true (L))))), cons false (cons true (cons true (cons false (cons true (cons false (R)))))), .C⟩ :=
    cross_r trans c5 (b) (cons false (cons true (cons false (cons true (L))))) (cons false (cons true (cons true (cons false (cons true (cons false (R)))))))
  have h6 : steps 12 ⟨rep (b) [false, true] (cons false (cons true (cons false (cons true (L))))), cons false (cons true (cons true (cons false (cons true (cons false (R)))))), .C⟩ = some ⟨cons false (cons true (cons false (cons true (rep (b) [false, true] (cons false (cons true (cons false (cons true (L))))))))), cons false (cons false (R)), .C⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (steps_seq trans h5 (h6)))))))

/-- The odd sweep at a block `0 1` with no pair: D(A+3,B) -> P(A+1,B+3), the parity tail, four 0s further right. -/
theorem m_odd_end0 (b : Nat) (L R : Tape) :
    steps (6 * b + 23) ⟨cons false (rep (b) [true, false] (cons true (cons true (cons true (L))))), cons false (cons false (cons true (cons false (cons false (cons false (cons false (cons false (R)))))))), .C⟩ = some ⟨cons false (cons true (cons true (cons true (cons true (cons false (cons true (rep (b) [false, true] (cons false (cons true (cons false (cons true (L)))))))))))), cons false (R), .C⟩ := by
  have hn : 2 + (0 + ((b) * 2 + (10 + (0 + ((b) * 4 + (11)))))) = 6 * b + 23 := by omega
  have h0 : steps 2 ⟨cons false (rep (b) [true, false] (cons true (cons true (cons true (L))))), cons false (cons false (cons true (cons false (cons false (cons false (cons false (cons false (R)))))))), .C⟩ = some ⟨cons false (rep (b) [true, false] (cons true (cons true (cons true (L))))), cons true (cons true (cons true (cons false (cons false (cons false (cons false (cons false (R)))))))), .E⟩ := rfl
  have h1 : steps 0 ⟨cons false (rep (b) [true, false] (cons true (cons true (cons true (L))))), cons true (cons true (cons true (cons false (cons false (cons false (cons false (cons false (R)))))))), .E⟩ = some ⟨rep (b) [false, true] (cons false (cons true (cons true (cons true (L))))), cons true (cons true (cons true (cons false (cons false (cons false (cons false (cons false (R)))))))), .E⟩ := by
    simp only [steps_zero, show cons false (rep (b) [true, false] (cons true (cons true (cons true (L))))) = rep (b) [false, true] (cons false (cons true (cons true (cons true (L))))) from
      rep_rotate (b) [false] [true, false] [false, true] rfl (cons true (cons true (cons true (L))))]
  have c2 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .E⟩ = some ⟨L, app [true] (app [true, false] R), .E⟩ := fun _ _ => rfl
  have h2 : steps ((b) * 2) ⟨rep (b) [false, true] (cons false (cons true (cons true (cons true (L))))), cons true (cons true (cons true (cons false (cons false (cons false (cons false (cons false (R)))))))), .E⟩ = some ⟨cons false (cons true (cons true (cons true (L)))), cons true (rep (b) [true, false] (cons true (cons true (cons false (cons false (cons false (cons false (cons false (R))))))))), .E⟩ :=
    cross_l trans c2 (b) (cons false (cons true (cons true (cons true (L))))) (cons true (cons true (cons false (cons false (cons false (cons false (cons false (R))))))))
  have h3 : steps 10 ⟨cons false (cons true (cons true (cons true (L)))), cons true (rep (b) [true, false] (cons true (cons true (cons false (cons false (cons false (cons false (cons false (R))))))))), .E⟩ = some ⟨cons false (cons true (cons false (cons true (L)))), cons false (rep (b) [true, false] (cons true (cons true (cons false (cons false (cons false (cons false (cons false (R))))))))), .C⟩ := rfl
  have h4 : steps 0 ⟨cons false (cons true (cons false (cons true (L)))), cons false (rep (b) [true, false] (cons true (cons true (cons false (cons false (cons false (cons false (cons false (R))))))))), .C⟩ = some ⟨cons false (cons true (cons false (cons true (L)))), rep (b) [false, true] (cons false (cons true (cons true (cons false (cons false (cons false (cons false (cons false (R))))))))), .C⟩ := by
    simp only [steps_zero, show cons false (rep (b) [true, false] (cons true (cons true (cons false (cons false (cons false (cons false (cons false (R))))))))) = rep (b) [false, true] (cons false (cons true (cons true (cons false (cons false (cons false (cons false (cons false (R))))))))) from
      rep_rotate (b) [false] [true, false] [false, true] rfl (cons true (cons true (cons false (cons false (cons false (cons false (cons false (R))))))))]
  have c5 : ∀ L R : Tape, steps 4 ⟨app [] L, app [false, true] R, .C⟩ = some ⟨app [] (app [false, true] L), R, .C⟩ := fun _ _ => rfl
  have h5 : steps ((b) * 4) ⟨cons false (cons true (cons false (cons true (L)))), rep (b) [false, true] (cons false (cons true (cons true (cons false (cons false (cons false (cons false (cons false (R))))))))), .C⟩ = some ⟨rep (b) [false, true] (cons false (cons true (cons false (cons true (L))))), cons false (cons true (cons true (cons false (cons false (cons false (cons false (cons false (R)))))))), .C⟩ :=
    cross_r trans c5 (b) (cons false (cons true (cons false (cons true (L))))) (cons false (cons true (cons true (cons false (cons false (cons false (cons false (cons false (R)))))))))
  have h6 : steps 11 ⟨rep (b) [false, true] (cons false (cons true (cons false (cons true (L))))), cons false (cons true (cons true (cons false (cons false (cons false (cons false (cons false (R)))))))), .C⟩ = some ⟨cons false (cons true (cons true (cons true (cons true (cons false (cons true (rep (b) [false, true] (cons false (cons true (cons false (cons true (L)))))))))))), cons false (R), .C⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (steps_seq trans h5 (h6)))))))

/-- The drain at a block `0 0 (10)^c 1` (a gap of two 0s): the block is merged, D(A+3,B) -> D(A+1,B+c+3). -/
theorem m_absorb (b c : Nat) (L R : Tape) :
    steps (6 * b + 4 * c + 20) ⟨cons false (rep (b) [true, false] (cons true (cons true (cons true (L))))), cons false (cons false (cons false (rep (c) [true, false] (cons true (cons false (R)))))), .C⟩ = some ⟨cons false (cons true (rep (c) [false, true] (cons false (cons true (rep (b) [false, true] (cons false (cons true (cons false (cons true (L)))))))))), cons false (R), .C⟩ := by
  have hn : 2 + (0 + ((b) * 2 + (10 + (0 + ((b) * 4 + (4 + (0 + ((c) * 4 + (4))))))))) = 6 * b + 4 * c + 20 := by omega
  have h0 : steps 2 ⟨cons false (rep (b) [true, false] (cons true (cons true (cons true (L))))), cons false (cons false (cons false (rep (c) [true, false] (cons true (cons false (R)))))), .C⟩ = some ⟨cons false (rep (b) [true, false] (cons true (cons true (cons true (L))))), cons true (cons true (cons false (rep (c) [true, false] (cons true (cons false (R)))))), .E⟩ := rfl
  have h1 : steps 0 ⟨cons false (rep (b) [true, false] (cons true (cons true (cons true (L))))), cons true (cons true (cons false (rep (c) [true, false] (cons true (cons false (R)))))), .E⟩ = some ⟨rep (b) [false, true] (cons false (cons true (cons true (cons true (L))))), cons true (cons true (cons false (rep (c) [true, false] (cons true (cons false (R)))))), .E⟩ := by
    simp only [steps_zero, show cons false (rep (b) [true, false] (cons true (cons true (cons true (L))))) = rep (b) [false, true] (cons false (cons true (cons true (cons true (L))))) from
      rep_rotate (b) [false] [true, false] [false, true] rfl (cons true (cons true (cons true (L))))]
  have c2 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .E⟩ = some ⟨L, app [true] (app [true, false] R), .E⟩ := fun _ _ => rfl
  have h2 : steps ((b) * 2) ⟨rep (b) [false, true] (cons false (cons true (cons true (cons true (L))))), cons true (cons true (cons false (rep (c) [true, false] (cons true (cons false (R)))))), .E⟩ = some ⟨cons false (cons true (cons true (cons true (L)))), cons true (rep (b) [true, false] (cons true (cons false (rep (c) [true, false] (cons true (cons false (R))))))), .E⟩ :=
    cross_l trans c2 (b) (cons false (cons true (cons true (cons true (L))))) (cons true (cons false (rep (c) [true, false] (cons true (cons false (R))))))
  have h3 : steps 10 ⟨cons false (cons true (cons true (cons true (L)))), cons true (rep (b) [true, false] (cons true (cons false (rep (c) [true, false] (cons true (cons false (R))))))), .E⟩ = some ⟨cons false (cons true (cons false (cons true (L)))), cons false (rep (b) [true, false] (cons true (cons false (rep (c) [true, false] (cons true (cons false (R))))))), .C⟩ := rfl
  have h4 : steps 0 ⟨cons false (cons true (cons false (cons true (L)))), cons false (rep (b) [true, false] (cons true (cons false (rep (c) [true, false] (cons true (cons false (R))))))), .C⟩ = some ⟨cons false (cons true (cons false (cons true (L)))), rep (b) [false, true] (cons false (cons true (cons false (rep (c) [true, false] (cons true (cons false (R))))))), .C⟩ := by
    simp only [steps_zero, show cons false (rep (b) [true, false] (cons true (cons false (rep (c) [true, false] (cons true (cons false (R))))))) = rep (b) [false, true] (cons false (cons true (cons false (rep (c) [true, false] (cons true (cons false (R))))))) from
      rep_rotate (b) [false] [true, false] [false, true] rfl (cons true (cons false (rep (c) [true, false] (cons true (cons false (R))))))]
  have c5 : ∀ L R : Tape, steps 4 ⟨app [] L, app [false, true] R, .C⟩ = some ⟨app [] (app [false, true] L), R, .C⟩ := fun _ _ => rfl
  have h5 : steps ((b) * 4) ⟨cons false (cons true (cons false (cons true (L)))), rep (b) [false, true] (cons false (cons true (cons false (rep (c) [true, false] (cons true (cons false (R))))))), .C⟩ = some ⟨rep (b) [false, true] (cons false (cons true (cons false (cons true (L))))), cons false (cons true (cons false (rep (c) [true, false] (cons true (cons false (R)))))), .C⟩ :=
    cross_r trans c5 (b) (cons false (cons true (cons false (cons true (L))))) (cons false (cons true (cons false (rep (c) [true, false] (cons true (cons false (R)))))))
  have h6 : steps 4 ⟨rep (b) [false, true] (cons false (cons true (cons false (cons true (L))))), cons false (cons true (cons false (rep (c) [true, false] (cons true (cons false (R)))))), .C⟩ = some ⟨cons false (cons true (rep (b) [false, true] (cons false (cons true (cons false (cons true (L))))))), cons false (rep (c) [true, false] (cons true (cons false (R)))), .C⟩ := rfl
  have h7 : steps 0 ⟨cons false (cons true (rep (b) [false, true] (cons false (cons true (cons false (cons true (L))))))), cons false (rep (c) [true, false] (cons true (cons false (R)))), .C⟩ = some ⟨cons false (cons true (rep (b) [false, true] (cons false (cons true (cons false (cons true (L))))))), rep (c) [false, true] (cons false (cons true (cons false (R)))), .C⟩ := by
    simp only [steps_zero, show cons false (rep (c) [true, false] (cons true (cons false (R)))) = rep (c) [false, true] (cons false (cons true (cons false (R)))) from
      rep_rotate (c) [false] [true, false] [false, true] rfl (cons true (cons false (R)))]
  have c8 : ∀ L R : Tape, steps 4 ⟨app [] L, app [false, true] R, .C⟩ = some ⟨app [] (app [false, true] L), R, .C⟩ := fun _ _ => rfl
  have h8 : steps ((c) * 4) ⟨cons false (cons true (rep (b) [false, true] (cons false (cons true (cons false (cons true (L))))))), rep (c) [false, true] (cons false (cons true (cons false (R)))), .C⟩ = some ⟨rep (c) [false, true] (cons false (cons true (rep (b) [false, true] (cons false (cons true (cons false (cons true (L)))))))), cons false (cons true (cons false (R))), .C⟩ :=
    cross_r trans c8 (c) (cons false (cons true (rep (b) [false, true] (cons false (cons true (cons false (cons true (L)))))))) (cons false (cons true (cons false (R))))
  have h9 : steps 4 ⟨rep (c) [false, true] (cons false (cons true (rep (b) [false, true] (cons false (cons true (cons false (cons true (L)))))))), cons false (cons true (cons false (R))), .C⟩ = some ⟨cons false (cons true (rep (c) [false, true] (cons false (cons true (rep (b) [false, true] (cons false (cons true (cons false (cons true (L)))))))))), cons false (R), .C⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (steps_seq trans h5 (steps_seq trans h6 (steps_seq trans h7 (steps_seq trans h8 (h9))))))))))

/-- End of an even drain: D(2,B) -> S = D(1,0) with a new block `0 (10)^(B+1) 1` in front of the rest. -/
theorem m_end2 (b : Nat) (R : Tape) :
    steps (2 * b + 11) ⟨cons false (rep (b) [true, false] (cons true (cons true (blank)))), cons false (cons false (R)), .C⟩ = some ⟨cons false (cons true (blank)), cons false (cons false (cons true (cons false (rep (b) [true, false] (cons true (R)))))), .C⟩ := by
  have hn : 2 + (0 + ((b) * 2 + (9))) = 2 * b + 11 := by omega
  have h0 : steps 2 ⟨cons false (rep (b) [true, false] (cons true (cons true (blank)))), cons false (cons false (R)), .C⟩ = some ⟨cons false (rep (b) [true, false] (cons true (cons true (blank)))), cons true (cons true (R)), .E⟩ := rfl
  have h1 : steps 0 ⟨cons false (rep (b) [true, false] (cons true (cons true (blank)))), cons true (cons true (R)), .E⟩ = some ⟨rep (b) [false, true] (cons false (cons true (cons true (blank)))), cons true (cons true (R)), .E⟩ := by
    simp only [steps_zero, show cons false (rep (b) [true, false] (cons true (cons true (blank)))) = rep (b) [false, true] (cons false (cons true (cons true (blank)))) from
      rep_rotate (b) [false] [true, false] [false, true] rfl (cons true (cons true (blank)))]
  have c2 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .E⟩ = some ⟨L, app [true] (app [true, false] R), .E⟩ := fun _ _ => rfl
  have h2 : steps ((b) * 2) ⟨rep (b) [false, true] (cons false (cons true (cons true (blank)))), cons true (cons true (R)), .E⟩ = some ⟨cons false (cons true (cons true (blank))), cons true (rep (b) [true, false] (cons true (R))), .E⟩ :=
    cross_l trans c2 (b) (cons false (cons true (cons true (blank)))) (cons true (R))
  have h3 : steps 9 ⟨cons false (cons true (cons true (blank))), cons true (rep (b) [true, false] (cons true (R))), .E⟩ = some ⟨cons false (cons true (blank)), cons false (cons false (cons true (cons false (rep (b) [true, false] (cons true (R)))))), .C⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (h3))))

/-- End of an odd drain: D(1,B) -> T(B+3), the head at the left end. -/
theorem m_end1 (b : Nat) (R : Tape) :
    steps (2 * b + 6) ⟨cons false (rep (b) [true, false] (cons true (blank))), cons false (cons false (R)), .C⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons false (rep (b) [true, false] (cons true (R))))))), .E⟩ := by
  have hn : 2 + (0 + ((b) * 2 + (4))) = 2 * b + 6 := by omega
  have h0 : steps 2 ⟨cons false (rep (b) [true, false] (cons true (blank))), cons false (cons false (R)), .C⟩ = some ⟨cons false (rep (b) [true, false] (cons true (blank))), cons true (cons true (R)), .E⟩ := rfl
  have h1 : steps 0 ⟨cons false (rep (b) [true, false] (cons true (blank))), cons true (cons true (R)), .E⟩ = some ⟨rep (b) [false, true] (cons false (cons true (blank))), cons true (cons true (R)), .E⟩ := by
    simp only [steps_zero, show cons false (rep (b) [true, false] (cons true (blank))) = rep (b) [false, true] (cons false (cons true (blank))) from
      rep_rotate (b) [false] [true, false] [false, true] rfl (cons true (blank))]
  have c2 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .E⟩ = some ⟨L, app [true] (app [true, false] R), .E⟩ := fun _ _ => rfl
  have h2 : steps ((b) * 2) ⟨rep (b) [false, true] (cons false (cons true (blank))), cons true (cons true (R)), .E⟩ = some ⟨cons false (cons true (blank)), cons true (rep (b) [true, false] (cons true (R))), .E⟩ :=
    cross_l trans c2 (b) (cons false (cons true (blank))) (cons true (R))
  have h3 : steps 4 ⟨cons false (cons true (blank)), cons true (rep (b) [true, false] (cons true (R))), .E⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons false (rep (b) [true, false] (cons true (R))))))), .E⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (h3))))

/-- D(0,B) -> T(B+2). -/
theorem m_end0 (b : Nat) (R : Tape) :
    steps (2 * b + 4) ⟨cons false (rep (b) [true, false] (blank)), cons false (cons false (R)), .C⟩ = some ⟨blank, cons false (cons true (cons false (rep (b) [true, false] (cons true (R))))), .E⟩ := by
  have hn : 2 + (0 + ((b) * 2 + (2))) = 2 * b + 4 := by omega
  have h0 : steps 2 ⟨cons false (rep (b) [true, false] (blank)), cons false (cons false (R)), .C⟩ = some ⟨cons false (rep (b) [true, false] (blank)), cons true (cons true (R)), .E⟩ := rfl
  have h1 : steps 0 ⟨cons false (rep (b) [true, false] (blank)), cons true (cons true (R)), .E⟩ = some ⟨rep (b) [false, true] (cons false (blank)), cons true (cons true (R)), .E⟩ := by
    simp only [steps_zero, show cons false (rep (b) [true, false] (blank)) = rep (b) [false, true] (cons false (blank)) from
      rep_rotate (b) [false] [true, false] [false, true] rfl (blank)]
  have c2 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .E⟩ = some ⟨L, app [true] (app [true, false] R), .E⟩ := fun _ _ => rfl
  have h2 : steps ((b) * 2) ⟨rep (b) [false, true] (cons false (blank)), cons true (cons true (R)), .E⟩ = some ⟨cons false (blank), cons true (rep (b) [true, false] (cons true (R))), .E⟩ :=
    cross_l trans c2 (b) (cons false (blank)) (cons true (R))
  have h3 : steps 2 ⟨cons false (blank), cons true (rep (b) [true, false] (cons true (R))), .E⟩ = some ⟨blank, cons false (cons true (cons false (rep (b) [true, false] (cons true (R))))), .E⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (h3))))

/-- T(n+1) next to a block `(10)^(y+1) 1`: the pairs become 1s, D(2n+1,0), and the block becomes `0 (10)^y 1`, ready for the odd sweeps (the ternary rounds). -/
theorem m_tseg (n y : Nat) (R : Tape) :
    steps (2 * n + 6) ⟨blank, rep (n + 1) [false, true] (rep (y + 1) [true, false] (cons true (R))), .E⟩ = some ⟨cons false (cons true (rep (n) [true, true] (blank))), cons false (cons false (rep (y) [true, false] (cons true (R)))), .C⟩ := by
  have hn : (n + 1) * 2 + (4) = 2 * n + 6 := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .E⟩ = some ⟨app [] (app [true, true] L), R, .E⟩ := fun _ _ => rfl
  have h0 : steps ((n + 1) * 2) ⟨blank, rep (n + 1) [false, true] (rep (y + 1) [true, false] (cons true (R))), .E⟩ = some ⟨rep (n + 1) [true, true] (blank), rep (y + 1) [true, false] (cons true (R)), .E⟩ :=
    cross_r trans c0 (n + 1) (blank) (rep (y + 1) [true, false] (cons true (R)))
  have h1 : steps 4 ⟨rep (n + 1) [true, true] (blank), rep (y + 1) [true, false] (cons true (R)), .E⟩ = some ⟨cons false (cons true (rep (n) [true, true] (blank))), cons false (cons false (rep (y) [true, false] (cons true (R)))), .C⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (h1))

/-- T(n+1) next to at least five 0s: D(2n+4,0), four 0s used. -/
theorem m_tblank (n : Nat) (R : Tape) :
    steps (2 * n + 5) ⟨blank, rep (n + 1) [false, true] (cons false (cons false (cons false (cons false (cons false (R)))))), .E⟩ = some ⟨cons false (cons true (cons true (rep (n + 1) [true, true] (blank)))), cons false (cons false (R)), .C⟩ := by
  have hn : (n + 1) * 2 + (3) = 2 * n + 5 := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .E⟩ = some ⟨app [] (app [true, true] L), R, .E⟩ := fun _ _ => rfl
  have h0 : steps ((n + 1) * 2) ⟨blank, rep (n + 1) [false, true] (cons false (cons false (cons false (cons false (cons false (R)))))), .E⟩ = some ⟨rep (n + 1) [true, true] (blank), cons false (cons false (cons false (cons false (cons false (R))))), .E⟩ :=
    cross_r trans c0 (n + 1) (blank) (cons false (cons false (cons false (cons false (cons false (R))))))
  have h1 : steps 3 ⟨rep (n + 1) [true, true] (blank), cons false (cons false (cons false (cons false (cons false (R))))), .E⟩ = some ⟨cons false (cons true (cons true (rep (n + 1) [true, true] (blank)))), cons false (cons false (R)), .C⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (h1))

/-- Parity tail with an even number of pairs: P(A+2,2k) -> D(A+1,2k+4), four 0s used. -/
theorem m_peven (a k : Nat) (R : Tape) :
    steps (22 * k + 44) ⟨cons false (cons true (cons true (cons true (rep (k) [true, false, true, false] (rep (a + 2) [true] (blank)))))), cons false (cons false (cons false (cons false (cons false (cons false (R)))))), .C⟩ = some ⟨cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (rep (k) [false, true, false, true] (cons false (cons true (rep (a) [true] (blank)))))))))))), cons false (cons false (R)), .C⟩ := by
  have hn : 24 + ((k) * 14 + (4 + (0 + ((k) * 8 + (16))))) = 22 * k + 44 := by omega
  have h0 : steps 24 ⟨cons false (cons true (cons true (cons true (rep (k) [true, false, true, false] (rep (a + 2) [true] (blank)))))), cons false (cons false (cons false (cons false (cons false (cons false (R)))))), .C⟩ = some ⟨rep (k) [true, false, true, false] (rep (a + 2) [true] (blank)), cons true (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons false (R)))))))))), .E⟩ := rfl
  have c1 : ∀ L R : Tape, steps 14 ⟨app [true, false, true, false] L, app [true] R, .E⟩ = some ⟨L, app [true] (app [true, false, true, false] R), .E⟩ := fun _ _ => rfl
  have h1 : steps ((k) * 14) ⟨rep (k) [true, false, true, false] (rep (a + 2) [true] (blank)), cons true (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons false (R)))))))))), .E⟩ = some ⟨rep (a + 2) [true] (blank), cons true (rep (k) [true, false, true, false] (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons false (R))))))))))), .E⟩ :=
    cross_l trans c1 (k) (rep (a + 2) [true] (blank)) (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons false (R))))))))))
  have h2 : steps 4 ⟨rep (a + 2) [true] (blank), cons true (rep (k) [true, false, true, false] (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons false (R))))))))))), .E⟩ = some ⟨cons false (cons true (rep (a) [true] (blank))), cons false (rep (k) [true, false, true, false] (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons false (R))))))))))), .C⟩ := rfl
  have h3 : steps 0 ⟨cons false (cons true (rep (a) [true] (blank))), cons false (rep (k) [true, false, true, false] (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons false (R))))))))))), .C⟩ = some ⟨cons false (cons true (rep (a) [true] (blank))), rep (k) [false, true, false, true] (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons false (R))))))))))), .C⟩ := by
    simp only [steps_zero, show cons false (rep (k) [true, false, true, false] (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons false (R))))))))))) = rep (k) [false, true, false, true] (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons false (R))))))))))) from
      rep_rotate (k) [false] [true, false, true, false] [false, true, false, true] rfl (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons false (R))))))))))]
  have c4 : ∀ L R : Tape, steps 8 ⟨app [] L, app [false, true, false, true] R, .C⟩ = some ⟨app [] (app [false, true, false, true] L), R, .C⟩ := fun _ _ => rfl
  have h4 : steps ((k) * 8) ⟨cons false (cons true (rep (a) [true] (blank))), rep (k) [false, true, false, true] (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons false (R))))))))))), .C⟩ = some ⟨rep (k) [false, true, false, true] (cons false (cons true (rep (a) [true] (blank)))), cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons false (R)))))))))), .C⟩ :=
    cross_r trans c4 (k) (cons false (cons true (rep (a) [true] (blank)))) (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons false (R)))))))))))
  have h5 : steps 16 ⟨rep (k) [false, true, false, true] (cons false (cons true (rep (a) [true] (blank)))), cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons false (R)))))))))), .C⟩ = some ⟨cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (rep (k) [false, true, false, true] (cons false (cons true (rep (a) [true] (blank)))))))))))), cons false (cons false (R)), .C⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (h5))))))

/-- Parity tail with an odd number of pairs: P(A,2k+1) -> S = D(1,0) followed by a gap `0^(A+1)` and the block `(10)^(2k+3) 1`: the block of 1s is wiped out and a new run starts from scratch inside the gap. -/
theorem m_podd (a k : Nat) (R : Tape) :
    steps (3 * a + 14 * k + 31) ⟨cons false (cons true (cons true (cons true (cons true (cons false (rep (k) [true, false, true, false] (rep (a) [true] (blank)))))))), cons false (cons false (cons false (cons false (R)))), .C⟩ = some ⟨cons false (cons true (blank)), rep (a) [false] (cons false (cons false (rep (k) [true, false, true, false] (cons true (cons false (cons true (cons false (cons true (cons false (cons true (R))))))))))), .C⟩ := by
  have hn : 24 + (0 + ((k) * 14 + (2 + ((a) * 3 + (5))))) = 3 * a + 14 * k + 31 := by omega
  have h0 : steps 24 ⟨cons false (cons true (cons true (cons true (cons true (cons false (rep (k) [true, false, true, false] (rep (a) [true] (blank)))))))), cons false (cons false (cons false (cons false (R)))), .C⟩ = some ⟨cons true (cons false (rep (k) [true, false, true, false] (rep (a) [true] (blank)))), cons true (cons true (cons false (cons true (cons false (cons true (cons false (cons true (R)))))))), .E⟩ := rfl
  have h1 : steps 0 ⟨cons true (cons false (rep (k) [true, false, true, false] (rep (a) [true] (blank)))), cons true (cons true (cons false (cons true (cons false (cons true (cons false (cons true (R)))))))), .E⟩ = some ⟨rep (k) [true, false, true, false] (cons true (cons false (rep (a) [true] (blank)))), cons true (cons true (cons false (cons true (cons false (cons true (cons false (cons true (R)))))))), .E⟩ := by
    simp only [steps_zero, show cons true (cons false (rep (k) [true, false, true, false] (rep (a) [true] (blank)))) = rep (k) [true, false, true, false] (cons true (cons false (rep (a) [true] (blank)))) from
      rep_rotate (k) [true, false] [true, false, true, false] [true, false, true, false] rfl (rep (a) [true] (blank))]
  have c2 : ∀ L R : Tape, steps 14 ⟨app [true, false, true, false] L, app [true] R, .E⟩ = some ⟨L, app [true] (app [true, false, true, false] R), .E⟩ := fun _ _ => rfl
  have h2 : steps ((k) * 14) ⟨rep (k) [true, false, true, false] (cons true (cons false (rep (a) [true] (blank)))), cons true (cons true (cons false (cons true (cons false (cons true (cons false (cons true (R)))))))), .E⟩ = some ⟨cons true (cons false (rep (a) [true] (blank))), cons true (rep (k) [true, false, true, false] (cons true (cons false (cons true (cons false (cons true (cons false (cons true (R))))))))), .E⟩ :=
    cross_l trans c2 (k) (cons true (cons false (rep (a) [true] (blank)))) (cons true (cons false (cons true (cons false (cons true (cons false (cons true (R))))))))
  have h3 : steps 2 ⟨cons true (cons false (rep (a) [true] (blank))), cons true (rep (k) [true, false, true, false] (cons true (cons false (cons true (cons false (cons true (cons false (cons true (R))))))))), .E⟩ = some ⟨rep (a) [true] (blank), cons false (cons false (cons false (rep (k) [true, false, true, false] (cons true (cons false (cons true (cons false (cons true (cons false (cons true (R))))))))))), .F⟩ := rfl
  have c4 : ∀ L R : Tape, steps 3 ⟨app [true] L, app [false] R, .F⟩ = some ⟨L, app [false] (app [false] R), .F⟩ := fun _ _ => rfl
  have h4 : steps ((a) * 3) ⟨rep (a) [true] (blank), cons false (cons false (cons false (rep (k) [true, false, true, false] (cons true (cons false (cons true (cons false (cons true (cons false (cons true (R))))))))))), .F⟩ = some ⟨blank, cons false (rep (a) [false] (cons false (cons false (rep (k) [true, false, true, false] (cons true (cons false (cons true (cons false (cons true (cons false (cons true (R)))))))))))), .F⟩ :=
    cross_l trans c4 (a) (blank) (cons false (cons false (rep (k) [true, false, true, false] (cons true (cons false (cons true (cons false (cons true (cons false (cons true (R)))))))))))
  have h5 : steps 5 ⟨blank, cons false (rep (a) [false] (cons false (cons false (rep (k) [true, false, true, false] (cons true (cons false (cons true (cons false (cons true (cons false (cons true (R)))))))))))), .F⟩ = some ⟨cons false (cons true (blank)), rep (a) [false] (cons false (cons false (rep (k) [true, false, true, false] (cons true (cons false (cons true (cons false (cons true (cons false (cons true (R))))))))))), .C⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (h5))))))

/-- The odd sweep at a block `0 1` followed by exactly three 0s and a 1: the parity tail has no room, and B reads a 1 (the machine halts on the next step, `tail_halts`). -/
theorem m_tail_halt (b : Nat) (L R : Tape) :
    steps (6 * b + 22) ⟨cons false (rep (b) [true, false] (cons true (cons true (cons true (L))))), cons false (cons false (cons true (cons false (cons false (cons false (cons true (R))))))), .C⟩ = some ⟨cons true (cons true (cons true (cons true (cons false (cons true (rep (b) [false, true] (cons false (cons true (cons false (cons true (L))))))))))), cons true (R), .B⟩ := by
  have hn : 2 + (0 + ((b) * 2 + (10 + (0 + ((b) * 4 + (10)))))) = 6 * b + 22 := by omega
  have h0 : steps 2 ⟨cons false (rep (b) [true, false] (cons true (cons true (cons true (L))))), cons false (cons false (cons true (cons false (cons false (cons false (cons true (R))))))), .C⟩ = some ⟨cons false (rep (b) [true, false] (cons true (cons true (cons true (L))))), cons true (cons true (cons true (cons false (cons false (cons false (cons true (R))))))), .E⟩ := rfl
  have h1 : steps 0 ⟨cons false (rep (b) [true, false] (cons true (cons true (cons true (L))))), cons true (cons true (cons true (cons false (cons false (cons false (cons true (R))))))), .E⟩ = some ⟨rep (b) [false, true] (cons false (cons true (cons true (cons true (L))))), cons true (cons true (cons true (cons false (cons false (cons false (cons true (R))))))), .E⟩ := by
    simp only [steps_zero, show cons false (rep (b) [true, false] (cons true (cons true (cons true (L))))) = rep (b) [false, true] (cons false (cons true (cons true (cons true (L))))) from
      rep_rotate (b) [false] [true, false] [false, true] rfl (cons true (cons true (cons true (L))))]
  have c2 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .E⟩ = some ⟨L, app [true] (app [true, false] R), .E⟩ := fun _ _ => rfl
  have h2 : steps ((b) * 2) ⟨rep (b) [false, true] (cons false (cons true (cons true (cons true (L))))), cons true (cons true (cons true (cons false (cons false (cons false (cons true (R))))))), .E⟩ = some ⟨cons false (cons true (cons true (cons true (L)))), cons true (rep (b) [true, false] (cons true (cons true (cons false (cons false (cons false (cons true (R)))))))), .E⟩ :=
    cross_l trans c2 (b) (cons false (cons true (cons true (cons true (L))))) (cons true (cons true (cons false (cons false (cons false (cons true (R)))))))
  have h3 : steps 10 ⟨cons false (cons true (cons true (cons true (L)))), cons true (rep (b) [true, false] (cons true (cons true (cons false (cons false (cons false (cons true (R)))))))), .E⟩ = some ⟨cons false (cons true (cons false (cons true (L)))), cons false (rep (b) [true, false] (cons true (cons true (cons false (cons false (cons false (cons true (R)))))))), .C⟩ := rfl
  have h4 : steps 0 ⟨cons false (cons true (cons false (cons true (L)))), cons false (rep (b) [true, false] (cons true (cons true (cons false (cons false (cons false (cons true (R)))))))), .C⟩ = some ⟨cons false (cons true (cons false (cons true (L)))), rep (b) [false, true] (cons false (cons true (cons true (cons false (cons false (cons false (cons true (R)))))))), .C⟩ := by
    simp only [steps_zero, show cons false (rep (b) [true, false] (cons true (cons true (cons false (cons false (cons false (cons true (R)))))))) = rep (b) [false, true] (cons false (cons true (cons true (cons false (cons false (cons false (cons true (R)))))))) from
      rep_rotate (b) [false] [true, false] [false, true] rfl (cons true (cons true (cons false (cons false (cons false (cons true (R)))))))]
  have c5 : ∀ L R : Tape, steps 4 ⟨app [] L, app [false, true] R, .C⟩ = some ⟨app [] (app [false, true] L), R, .C⟩ := fun _ _ => rfl
  have h5 : steps ((b) * 4) ⟨cons false (cons true (cons false (cons true (L)))), rep (b) [false, true] (cons false (cons true (cons true (cons false (cons false (cons false (cons true (R)))))))), .C⟩ = some ⟨rep (b) [false, true] (cons false (cons true (cons false (cons true (L))))), cons false (cons true (cons true (cons false (cons false (cons false (cons true (R))))))), .C⟩ :=
    cross_r trans c5 (b) (cons false (cons true (cons false (cons true (L))))) (cons false (cons true (cons true (cons false (cons false (cons false (cons true (R))))))))
  have h6 : steps 10 ⟨rep (b) [false, true] (cons false (cons true (cons false (cons true (L))))), cons false (cons true (cons true (cons false (cons false (cons false (cons true (R))))))), .C⟩ = some ⟨cons true (cons true (cons true (cons true (cons false (cons true (rep (b) [false, true] (cons false (cons true (cons false (cons true (L))))))))))), cons true (R), .B⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (steps_seq trans h5 (h6)))))))

end H8002
