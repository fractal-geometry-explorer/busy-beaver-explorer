import Blank
import Rules

/-! What each theorem rests on: `lean Axioms.lean` prints the axioms. `propext` and `Quot.sound` are the standard ones;
a `native_decide` axiom means the theorem also trusts Lean's compiler. -/

#print axioms BB6b.blank_runs_20000
#print axioms BB6b.blank_runs_10M
#print axioms BB6b.a_sweep
#print axioms BB6b.b_sweep
