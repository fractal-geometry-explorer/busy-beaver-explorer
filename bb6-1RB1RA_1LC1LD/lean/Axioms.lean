import Blank
import Macro

/-! What each theorem rests on: `lean Axioms.lean` prints the axioms. `propext` and `Quot.sound` are the standard ones;
a `native_decide` axiom means the theorem also trusts Lean's compiler. -/

#print axioms BB6c.step_none_iff
#print axioms BB6c.halt_shape
#print axioms BB6c.blank_at_46
#print axioms BB6c.blank_runs_20000
#print axioms BB6c.blank_runs_10M

-- Macro.lean: the pass from one right-end configuration to the next (kernel only)
#print axioms BB6c.next_sound
#print axioms BB6c.K_zero_halts
#print axioms BB6c.halts_of_reaches
#print axioms BB6c.blank_passes
