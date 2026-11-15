import Machine

/-!
# 1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA---: the machine as twelve local rewriting rules

Every run of the machine is a sequence of the moves below (each for arbitrary tapes `L`, `R` on both sides), so the
machine is a rewriting system on two stacks: the tape left of the head and the tape right of it.

Right-moving states read the right tape (`X> w` is state X with `w` under and right of the head):

    A> 00  ->  <B 01         (aa00: the head turns; B stands on the cell left of the two cells)
    A> 01  ->  01 A>         (aa01: A hops over a pair 01)
    A> 10  ->  10 C>         (aa10)
    A> 110 ->  101 A>        (aa110)
    A> 111     halts         (aa111: the only way to halt)
    C> 0   ->  1 D>          (cc0)
    C> 1   ->  <B 0          (cc1: the head turns)
    D> 0   ->  0 A>          (dd0)
    D> 1   ->  1 C>          (dd1)

State B standing on a cell reads that cell and its left neighbour (`cb <B`: B on b, c left of it):

    10 <B  ->  <B 01         (bb10: the pair is flipped and goes to the right tape, B moves on to the left)
    00 <B  ->  11 C>         (bb00)
    01 <B  ->  01 D>         (bb01)
    11 <B  ->  01 A>         (bb11)

The cells written to the right tape are only `01` (aa00, bb10) and `0` (cc1).  `py/macro.py` runs these rules and
compares them with the plain machine.
-/

namespace H116343

open TM

theorem aa00 (x : Bool) (L R : Tape) :
    steps 3 ⟨cons x L, cons false (cons false R), .A⟩ = some ⟨L, cons x (cons false (cons true R)), .B⟩ := rfl

theorem aa01 (L R : Tape) :
    steps 4 ⟨L, cons false (cons true R), .A⟩ = some ⟨cons true (cons false L), R, .A⟩ := rfl

theorem aa10 (L R : Tape) :
    steps 2 ⟨L, cons true (cons false R), .A⟩ = some ⟨cons false (cons true L), R, .C⟩ := rfl

theorem aa110 (L R : Tape) :
    steps 3 ⟨L, cons true (cons true (cons false R)), .A⟩ = some ⟨cons true (cons false (cons true L)), R, .A⟩ := rfl

/-- `A> 111` halts: after two steps the machine is in state F on a 1. -/
theorem aa111 (L R : Tape) :
    steps 2 ⟨L, cons true (cons true (cons true R)), .A⟩ = some ⟨cons false (cons true L), cons true R, .F⟩ ∧
      step ⟨cons false (cons true L), cons true R, .F⟩ = none := ⟨rfl, rfl⟩

theorem cc0 (L R : Tape) :
    steps 1 ⟨L, cons false R, .C⟩ = some ⟨cons true L, R, .D⟩ := rfl

theorem cc1 (x : Bool) (L R : Tape) :
    steps 1 ⟨cons x L, cons true R, .C⟩ = some ⟨L, cons x (cons false R), .B⟩ := rfl

theorem dd0 (L R : Tape) :
    steps 1 ⟨L, cons false R, .D⟩ = some ⟨cons false L, R, .A⟩ := rfl

theorem dd1 (L R : Tape) :
    steps 1 ⟨L, cons true R, .D⟩ = some ⟨cons true L, R, .C⟩ := rfl

theorem bb10 (x : Bool) (L R : Tape) :
    steps 2 ⟨cons true (cons x L), cons false R, .B⟩ = some ⟨L, cons x (cons false (cons true R)), .B⟩ := rfl

theorem bb00 (L R : Tape) :
    steps 3 ⟨cons false L, cons false R, .B⟩ = some ⟨cons true (cons true L), R, .C⟩ := rfl

theorem bb01 (L R : Tape) :
    steps 3 ⟨cons false L, cons true R, .B⟩ = some ⟨cons true (cons false L), R, .D⟩ := rfl

theorem bb11 (L R : Tape) :
    steps 3 ⟨cons true L, cons true R, .B⟩ = some ⟨cons true (cons false L), R, .A⟩ := rfl

end H116343
