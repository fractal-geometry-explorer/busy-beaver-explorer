import Blank
import Rules
import MacroRun
import Wave
import Events
import DeepMind
import WaveTime
import Periods
import Monotone

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
#print axioms BB6b.carry_wave
#print axioms BB6b.super_run
#print axioms BB6b.superL_none_iff
#print axioms BB6b.halts_iff_pow2
#print axioms BB6b.halts_iff_pow2'
#print axioms BB6b.orbit_tape
#print axioms BB6b.ev_sound
#print axioms BB6b.ev4
#print axioms BB6b.halts_iff_ev
#print axioms BB6b.evOrbit_tape
#print axioms BB6b.highLevelNext_eq
#print axioms BB6b.halts_iff_hl
#print axioms BB6b.carry_wave_t
#print axioms BB6b.super_steps
#print axioms BB6b.orbitT_steps
#print axioms BB6b.orbitT_halt
#print axioms BB6b.runs_of_orbitT

#print axioms BB6b.cycle_residues
#print axioms BB6b.period_factor
#print axioms BB6b.level_period
#print axioms BB6b.rule₃

#print axioms BB6b.superL_grows
#print axioms BB6b.orbit_grows
#print axioms BB6b.blank_orbit_grows
