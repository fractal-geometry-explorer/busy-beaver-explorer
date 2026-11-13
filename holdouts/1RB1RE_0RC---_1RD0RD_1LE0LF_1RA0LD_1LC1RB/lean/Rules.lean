import Machine

/-! # Sweep rules of 1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB

The right part of the tape is a block of 1s followed by pairs 01. One round trip of the head from the right end takes two 1s off the block and adds two pairs (`sweep`): a leftward run of E and D turns each pair 01 into 10 on the way to the block, and a rightward zigzag of F, B, C, D turns them back.

Written by `bbtools.symtm.prove` (the trace of a symbolic run, checked by the kernel). -/

namespace H8002

open TM

/-- One round trip from the right end: `1^(a+4) (01)^b 0 C>0` becomes `1^(a+2) (01)^(b+2) 0 C>0` (the run writes it as `1^a 1 1 0 1 0 (10)^b 1 0 C>`). -/
theorem sweep (a b : Nat) (L : Tape) :
    steps (6 * b + 16) ⟨cons false (rep (b) [true, false] (cons true (cons true (cons true (cons true (rep (a) [true] (L))))))), cons false (blank), .C⟩ = some ⟨cons false (cons true (rep (b) [false, true] (cons false (cons true (cons false (cons true (cons true (rep (a) [true] (L))))))))), blank, .C⟩ := by
  have h0 : steps 3 ⟨cons false (rep (b) [true, false] (cons true (cons true (cons true (cons true (rep (a) [true] (L))))))), cons false (blank), .C⟩ = some ⟨rep (b) [true, false] (cons true (cons true (cons true (cons true (rep (a) [true] (L)))))), cons false (cons false (cons true (blank))), .D⟩ := rfl
  have c1 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .D⟩ = some ⟨L, app [false] (app [false, true] R), .D⟩ := fun _ _ => rfl
  have h1 : steps ((b) * 2) ⟨rep (b) [true, false] (cons true (cons true (cons true (cons true (rep (a) [true] (L)))))), cons false (cons false (cons true (blank))), .D⟩ = some ⟨cons true (cons true (cons true (cons true (rep (a) [true] (L))))), cons false (rep (b) [false, true] (cons false (cons true (blank)))), .D⟩ :=
    cross_l trans c1 (b) (cons true (cons true (cons true (cons true (rep (a) [true] (L)))))) (cons false (cons true (blank)))
  have h2 : steps 9 ⟨cons true (cons true (cons true (cons true (rep (a) [true] (L))))), cons false (rep (b) [false, true] (cons false (cons true (blank)))), .D⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (rep (a) [true] (L)))))), rep (b) [false, true] (cons false (cons true (blank))), .C⟩ := rfl
  have c3 : ∀ L R : Tape, steps 4 ⟨app [] L, app [false, true] R, .C⟩ = some ⟨app [] (app [false, true] L), R, .C⟩ := fun _ _ => rfl
  have h3 : steps ((b) * 4) ⟨cons false (cons true (cons false (cons true (cons true (rep (a) [true] (L)))))), rep (b) [false, true] (cons false (cons true (blank))), .C⟩ = some ⟨rep (b) [false, true] (cons false (cons true (cons false (cons true (cons true (rep (a) [true] (L))))))), cons false (cons true (blank)), .C⟩ :=
    cross_r trans c3 (b) (cons false (cons true (cons false (cons true (cons true (rep (a) [true] (L))))))) (cons false (cons true (blank)))
  have h4 : steps 4 ⟨rep (b) [false, true] (cons false (cons true (cons false (cons true (cons true (rep (a) [true] (L))))))), cons false (cons true (blank)), .C⟩ = some ⟨cons false (cons true (rep (b) [false, true] (cons false (cons true (cons false (cons true (cons true (rep (a) [true] (L))))))))), blank, .C⟩ := rfl
  exact steps_congr trans (a := 3 + ((b) * 2 + (9 + ((b) * 4 + (4))))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))


end H8002
