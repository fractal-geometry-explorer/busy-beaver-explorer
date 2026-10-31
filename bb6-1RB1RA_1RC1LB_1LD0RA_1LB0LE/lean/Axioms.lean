import Blank
import Rules
import Pass
import Front

/-! What each theorem rests on: `lean Axioms.lean` prints the axioms. `propext` and `Quot.sound` are the standard ones;
a `native_decide` axiom means the theorem also trusts Lean's compiler. -/

#print axioms BB6d.step_none_iff
#print axioms BB6d.halt_shape
#print axioms BB6d.blank_at_17
#print axioms BB6d.blank_runs_20000
#print axioms BB6d.blank_runs_10M
#print axioms BB6d.start
#print axioms BB6d.de_sweep
#print axioms BB6d.de_sweep_odd
#print axioms BB6d.e_cross
#print axioms BB6d.d_stop
#print axioms BB6d.zig
#print axioms BB6d.d_stop_empty
#print axioms BB6d.zig_empty
#print axioms BB6d.turn
#print axioms BB6d.pass
#print axioms BB6d.pass_halt
#print axioms BB6d.next_sum
#print axioms BB6d.next_halt_odd
#print axioms BB6d.orbit_ok
#print axioms BB6d.orbit_ne_halt
#print axioms BB6d.halts_only_by_one
#print axioms BB6d.never_halts_of_no_one
#print axioms BB6d.orbit_12
#print axioms BB6d.next_good
#print axioms BB6d.orbit_good
#print axioms BB6d.one_front
#print axioms BB6d.front_twice
#print axioms BB6d.orbit_front_twice
#print axioms BB6d.halts_only_at_front
