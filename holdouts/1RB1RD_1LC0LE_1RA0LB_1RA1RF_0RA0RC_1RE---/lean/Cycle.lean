import Machine

/-!
# 1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---: the cycle of a phase

Between two visits of the right end in state D, the tape `P 0 1^m (01)^y 1 D>0` loses three 1s of its block and gains
four `01` pairs (`cycle`, for all `x y` and any tape `L` left of the block). A phase repeats this until fewer than
three 1s are left; what happens then depends on `m mod 3` and the prefix `P` (see the README), and is not proved here.

Written by `bbtools.symtm.prove`; checked by the kernel (`rfl` steps and the shift rules of `TM.Basic`).
-/

namespace H58362

open TM

/-- One cycle of a phase: three 1s of the block become four more 01 pairs, in 6y+39 steps. -/
theorem cycle (x y : Nat) (L : Tape) :
    steps (6 * y + 39) ⟨cons true (rep (y) [true, false] (rep (x + 3) [true] (L))), blank, .D⟩ = some ⟨cons true (cons true (cons false (cons true (cons false (rep (y) [true, false] (cons true (cons false (cons true (cons false (rep (x) [true] (L))))))))))), blank, .D⟩ := by
  have h0 : steps 21 ⟨cons true (rep (y) [true, false] (rep (x + 3) [true] (L))), blank, .D⟩ = some ⟨rep (y) [true, false] (rep (x + 3) [true] (L)), cons false (cons false (cons true (cons false (cons true (cons true (blank)))))), .B⟩ := rfl
  have c1 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .B⟩ = some ⟨L, app [false] (app [false, true] R), .B⟩ := fun _ _ => rfl
  have h1 : steps ((y) * 2) ⟨rep (y) [true, false] (rep (x + 3) [true] (L)), cons false (cons false (cons true (cons false (cons true (cons true (blank)))))), .B⟩ = some ⟨rep (x + 3) [true] (L), cons false (rep (y) [false, true] (cons false (cons true (cons false (cons true (cons true (blank))))))), .B⟩ :=
    cross_l trans c1 (y) (rep (x + 3) [true] (L)) (cons false (cons true (cons false (cons true (cons true (blank))))))
  have h2 : steps 9 ⟨rep (x + 3) [true] (L), cons false (rep (y) [false, true] (cons false (cons true (cons false (cons true (cons true (blank))))))), .B⟩ = some ⟨cons true (cons false (cons true (cons false (rep (x) [true] (L))))), rep (y) [false, true] (cons false (cons true (cons false (cons true (cons true (blank)))))), .A⟩ := rfl
  have c3 : ∀ L R : Tape, steps 4 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [true, false] L), R, .A⟩ := fun _ _ => rfl
  have h3 : steps ((y) * 4) ⟨cons true (cons false (cons true (cons false (rep (x) [true] (L))))), rep (y) [false, true] (cons false (cons true (cons false (cons true (cons true (blank)))))), .A⟩ = some ⟨rep (y) [true, false] (cons true (cons false (cons true (cons false (rep (x) [true] (L)))))), cons false (cons true (cons false (cons true (cons true (blank))))), .A⟩ :=
    cross_r trans c3 (y) (cons true (cons false (cons true (cons false (rep (x) [true] (L)))))) (cons false (cons true (cons false (cons true (cons true (blank))))))
  have h4 : steps 9 ⟨rep (y) [true, false] (cons true (cons false (cons true (cons false (rep (x) [true] (L)))))), cons false (cons true (cons false (cons true (cons true (blank))))), .A⟩ = some ⟨cons true (cons true (cons false (cons true (cons false (rep (y) [true, false] (cons true (cons false (cons true (cons false (rep (x) [true] (L))))))))))), blank, .D⟩ := rfl
  exact steps_congr trans (a := 21 + ((y) * 2 + (9 + ((y) * 4 + (9))))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))


end H58362
