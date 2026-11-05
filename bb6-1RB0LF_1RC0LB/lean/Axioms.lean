import Blank
import Pass
import Macro
import Counter
import MacroRun

/-! What each theorem rests on: `lean Axioms.lean` prints the axioms. `propext` and `Quot.sound` are the standard ones;
a `native_decide` axiom means the theorem also trusts Lean's compiler. -/

#print axioms BB6e.step_none_iff
#print axioms BB6e.halt_shape
#print axioms BB6e.blank_at_63
#print axioms BB6e.blank_runs_20000
#print axioms BB6e.blank_runs_10M
#print axioms BB6e.pass
#print axioms BB6e.pass_outcome
#print axioms BB6e.sweep
#print axioms BB6e.erase
#print axioms BB6e.mstep_sound
#print axioms BB6e.blank_to_M0
#print axioms BB6e.no_halt_of_macro
#print axioms BB6e.fscan_phi
#print axioms BB6e.phi_interior
#print axioms BB6e.phi_end
#print axioms BB6e.phi_bottom
#print axioms BB6e.mok_iff
#print axioms BB6e.macro_runs_100M
#print axioms BB6e.blank_runs_macro_100M
