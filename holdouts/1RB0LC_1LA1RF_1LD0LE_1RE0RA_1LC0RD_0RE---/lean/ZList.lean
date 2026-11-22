import Collisions
import Movers

/-!
# The right end after a collision: any list of swept movers

When a collision at the right end sends the head back right through the part it has just swept, the tape on its
right is a list of swept movers `1 (10)^(g+2)`, each with a gap of at least two pairs, then a last one `1 (10)^1`
and blank tape.  The lemmas of `Collisions.lean` stop at the second swept mover; `zb_cells` turns each into a mover
at rest and `ze_cells` the last one.  Here they are chained over any list: the head comes out at the right end in
state E, with every swept mover turned into a mover at rest.  Checked by Lean's kernel.
-/

namespace H71372

open TM

/-- Swept movers on the right of the head, the leftmost first: `1 (10)^(g+2)` each. -/
def zbl : List Nat → Tape → Tape
  | [], R => R
  | g :: gs, R => cons true (rep (g + 2) [true, false] (zbl gs R))

/-- The cost of the sweep over them. -/
def zcost : List Nat → Nat
  | [] => 0
  | g :: gs => 2 * g + 5 + zcost gs

/-- The sweep turns every swept mover into a mover at rest with two pairs less of gap. -/
theorem zlist (gs : List Nat) (R : Tape) : ∀ L : Tape,
    steps (zcost gs) ⟨L, zbl gs R, .E⟩ = some ⟨movers gs.reverse L, R, .E⟩ := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h1 : steps (2 * g + 5) ⟨L, zbl (g :: gs) R, .E⟩ = some ⟨mv g L, zbl gs R, .E⟩ := zb_cells g L (zbl gs R)
    have h2 := ih (mv g L)
    have e : movers (g :: gs).reverse L = movers gs.reverse (mv g L) := by
      simp only [List.reverse_cons, movers_append]; rfl
    rw [e]
    exact steps_seq trans h1 h2

/-- The whole right end: the list, then the last swept mover with its one-pair gap, then blank tape. -/
theorem zend (gs : List Nat) (L : Tape) :
    steps (zcost gs + 5) ⟨L, zbl gs (cons true (cons true (cons false (cons true blank)))), .E⟩ =
      some ⟨mv 0 (movers gs.reverse L), blank, .E⟩ :=
  steps_seq trans (zlist gs _ L) (ze_cells _)

end H71372
