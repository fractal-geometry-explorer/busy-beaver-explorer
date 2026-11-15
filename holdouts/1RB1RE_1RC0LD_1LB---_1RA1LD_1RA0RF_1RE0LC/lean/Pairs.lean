import Machine

/-! The pair machine of 1RB1RE_1RC0LD_1LB---_1RA1LD_1RA0RF_1RE0LC: every macro move on a pair of cells (0 = 01, 1 = 11, a = 10, b = 00), for every
tape around it. `r_X_s`: state X on the first cell of the pair s to its right; `l_X_s`: state X on the second
cell of the pair s to its left. Written by `py/pairs.py`; each is checked by the kernel by running the steps. -/

namespace H151599

open TM

theorem r_A_0 (y : Bool) (L R : Tape) :
    steps 3 ⟨cons y L, cons false (cons true R), .A⟩ = some ⟨L, cons y (cons true (cons false R)), .D⟩ := rfl

theorem r_A_1 (L R : Tape) :
    steps 2 ⟨L, cons true (cons true R), .A⟩ = some ⟨cons false (cons true L), R, .F⟩ := rfl

theorem r_A_a (L R : Tape) :
    steps 2 ⟨L, cons true (cons false R), .A⟩ = some ⟨cons true (cons true L), R, .A⟩ := rfl

theorem r_A_b (L R : Tape) :
    steps 2 ⟨L, cons false (cons false R), .A⟩ = some ⟨cons true (cons true L), R, .C⟩ := rfl

theorem r_B_1 (y : Bool) (L R : Tape) :
    steps 1 ⟨cons y L, cons true (cons true R), .B⟩ = some ⟨L, cons y (cons false (cons true R)), .D⟩ := rfl

theorem r_B_a (y : Bool) (L R : Tape) :
    steps 1 ⟨cons y L, cons true (cons false R), .B⟩ = some ⟨L, cons y (cons false (cons false R)), .D⟩ := rfl

theorem r_B_b (y : Bool) (L R : Tape) :
    steps 3 ⟨cons y L, cons false (cons false R), .B⟩ = some ⟨L, cons y (cons false (cons true R)), .D⟩ := rfl

theorem r_C_0 (y : Bool) (L R : Tape) :
    steps 1 ⟨cons y L, cons false (cons true R), .C⟩ = some ⟨L, cons y (cons true (cons true R)), .B⟩ := rfl

theorem r_C_b (y : Bool) (L R : Tape) :
    steps 1 ⟨cons y L, cons false (cons false R), .C⟩ = some ⟨L, cons y (cons true (cons false R)), .B⟩ := rfl

theorem r_D_0 (L R : Tape) :
    steps 2 ⟨L, cons false (cons true R), .D⟩ = some ⟨cons true (cons true L), R, .E⟩ := rfl

theorem r_D_1 (y : Bool) (L R : Tape) :
    steps 1 ⟨cons y L, cons true (cons true R), .D⟩ = some ⟨L, cons y (cons true (cons true R)), .D⟩ := rfl

theorem r_D_a (y : Bool) (L R : Tape) :
    steps 1 ⟨cons y L, cons true (cons false R), .D⟩ = some ⟨L, cons y (cons true (cons false R)), .D⟩ := rfl

theorem r_D_b (L R : Tape) :
    steps 2 ⟨L, cons false (cons false R), .D⟩ = some ⟨cons true (cons true L), R, .B⟩ := rfl

theorem r_E_0 (L R : Tape) :
    steps 2 ⟨L, cons false (cons true R), .E⟩ = some ⟨cons true (cons true L), R, .E⟩ := rfl

theorem r_E_1 (y : Bool) (L R : Tape) :
    steps 3 ⟨cons y L, cons true (cons true R), .E⟩ = some ⟨L, cons y (cons true (cons false R)), .B⟩ := rfl

theorem r_E_a (L R : Tape) :
    steps 2 ⟨L, cons true (cons false R), .E⟩ = some ⟨cons true (cons false L), R, .E⟩ := rfl

theorem r_E_b (L R : Tape) :
    steps 2 ⟨L, cons false (cons false R), .E⟩ = some ⟨cons true (cons true L), R, .B⟩ := rfl

theorem r_F_0 (L R : Tape) :
    steps 2 ⟨L, cons false (cons true R), .F⟩ = some ⟨cons false (cons true L), R, .F⟩ := rfl

theorem r_F_1 (y : Bool) (L R : Tape) :
    steps 1 ⟨cons y L, cons true (cons true R), .F⟩ = some ⟨L, cons y (cons false (cons true R)), .C⟩ := rfl

theorem r_F_a (y : Bool) (L R : Tape) :
    steps 1 ⟨cons y L, cons true (cons false R), .F⟩ = some ⟨L, cons y (cons false (cons false R)), .C⟩ := rfl

theorem r_F_b (L R : Tape) :
    steps 2 ⟨L, cons false (cons false R), .F⟩ = some ⟨cons true (cons true L), R, .A⟩ := rfl

theorem l_A_0 (L R : Tape) :
    steps 1 ⟨cons false L, cons true R, .A⟩ = some ⟨cons true (cons false L), R, .E⟩ := rfl

theorem l_A_1 (L R : Tape) :
    steps 1 ⟨cons true L, cons true R, .A⟩ = some ⟨cons true (cons true L), R, .E⟩ := rfl

theorem l_A_a (L R : Tape) :
    steps 1 ⟨cons true L, cons false R, .A⟩ = some ⟨cons true (cons true L), R, .B⟩ := rfl

theorem l_A_b (L R : Tape) :
    steps 1 ⟨cons false L, cons false R, .A⟩ = some ⟨cons true (cons false L), R, .B⟩ := rfl

theorem l_B_0 (L R : Tape) :
    steps 3 ⟨cons false L, cons true R, .B⟩ = some ⟨cons true (cons true L), R, .B⟩ := rfl

theorem l_B_1 (y : Bool) (L R : Tape) :
    steps 2 ⟨cons true (cons y L), cons true R, .B⟩ = some ⟨L, cons y (cons true (cons false R)), .D⟩ := rfl

theorem l_B_a (L R : Tape) :
    steps 1 ⟨cons true L, cons false R, .B⟩ = some ⟨cons true (cons true L), R, .C⟩ := rfl

theorem l_B_b (L R : Tape) :
    steps 1 ⟨cons false L, cons false R, .B⟩ = some ⟨cons true (cons false L), R, .C⟩ := rfl

theorem l_C_a (y : Bool) (L R : Tape) :
    steps 2 ⟨cons true (cons y L), cons false R, .C⟩ = some ⟨L, cons y (cons false (cons true R)), .D⟩ := rfl

theorem l_D_0 (L R : Tape) :
    steps 3 ⟨cons false L, cons true R, .D⟩ = some ⟨cons true (cons true L), R, .E⟩ := rfl

theorem l_D_1 (y : Bool) (L R : Tape) :
    steps 2 ⟨cons true (cons y L), cons true R, .D⟩ = some ⟨L, cons y (cons true (cons true R)), .D⟩ := rfl

theorem l_D_a (L R : Tape) :
    steps 1 ⟨cons true L, cons false R, .D⟩ = some ⟨cons true (cons true L), R, .A⟩ := rfl

theorem l_D_b (L R : Tape) :
    steps 1 ⟨cons false L, cons false R, .D⟩ = some ⟨cons true (cons false L), R, .A⟩ := rfl

theorem l_E_0 (L R : Tape) :
    steps 1 ⟨cons false L, cons true R, .E⟩ = some ⟨cons false (cons false L), R, .F⟩ := rfl

theorem l_E_1 (L R : Tape) :
    steps 1 ⟨cons true L, cons true R, .E⟩ = some ⟨cons false (cons true L), R, .F⟩ := rfl

theorem l_E_a (L R : Tape) :
    steps 1 ⟨cons true L, cons false R, .E⟩ = some ⟨cons true (cons true L), R, .A⟩ := rfl

theorem l_E_b (L R : Tape) :
    steps 1 ⟨cons false L, cons false R, .E⟩ = some ⟨cons true (cons false L), R, .A⟩ := rfl

theorem l_F_0 (y : Bool) (L R : Tape) :
    steps 2 ⟨cons false (cons y L), cons true R, .F⟩ = some ⟨L, cons y (cons true (cons false R)), .B⟩ := rfl

theorem l_F_a (L R : Tape) :
    steps 1 ⟨cons true L, cons false R, .F⟩ = some ⟨cons true (cons true L), R, .E⟩ := rfl

theorem l_F_b (L R : Tape) :
    steps 1 ⟨cons false L, cons false R, .F⟩ = some ⟨cons true (cons false L), R, .E⟩ := rfl

end H151599
