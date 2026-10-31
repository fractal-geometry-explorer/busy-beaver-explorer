import Blank
import Edge

/-! What each theorem rests on: `lean Axioms.lean` prints the axioms. `propext` and `Quot.sound` are the standard ones;
a `native_decide` axiom means the theorem also trusts Lean's compiler. -/

#print axioms BB6c.step_none_iff
#print axioms BB6c.halt_shape
#print axioms BB6c.blank_at_46
#print axioms BB6c.blank_runs_20000
#print axioms BB6c.blank_runs_10M
#print axioms BB6c.d_one_right
#print axioms BB6c.d_left_end
#print axioms BB6c.reach_inv
#print axioms BB6c.right_no_double_zero
#print axioms BB6c.halt_at_edge
#print axioms BB6c.d_zero_zero
#print axioms BB6c.halts_iff_edge
