import Blank
import Rules
import MacroRun

/-! What each theorem rests on: `lean Axioms.lean` prints the axioms. `propext` and `Quot.sound` are the standard ones;
a `native_decide` axiom means the theorem also trusts Lean's compiler. -/

#print axioms BB6b.blank_runs_20000
#print axioms BB6b.blank_runs_10M
#print axioms BB6b.a_sweep
#print axioms BB6b.b_sweep
#print axioms BB6b.transfer
#print axioms BB6b.empty_start
#print axioms BB6b.sweep_step
#print axioms BB6b.carry_start
#print axioms BB6b.carry_two
#print axioms BB6b.carry_exit
#print axioms BB6b.carry_one
#print axioms BB6b.next_sound
#print axioms BB6b.next_halt_iff
#print axioms BB6b.runM_sound
#print axioms BB6b.halts_iff
#print axioms BB6b.runM_1000
#print axioms BB6b.blank_runs_2e10
#print axioms BB6b.blank_runs_9e13
