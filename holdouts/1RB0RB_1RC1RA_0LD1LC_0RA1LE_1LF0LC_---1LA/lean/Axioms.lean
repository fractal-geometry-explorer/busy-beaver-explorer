import OrbitRun
import ZoneRun
import ZoneCascade
import Shield

/-! The axioms behind the main results: `propext`, `Quot.sound` and `Classical.choice` for the kernel-checked
theorems, and in addition the auxiliary axiom that `native_decide` adds for `orbit_runs` and
`blank_runs_orbit`. -/

#print axioms H25821.mstep_sound
#print axioms H25821.orbT_sound
#print axioms H25821.halts_iff
#print axioms H25821.orbit_runs
#print axioms H25821.blank_runs_orbit
#print axioms XS.zone_step
#print axioms XS.swr_split
#print axioms XS.swr_append_ok
#print axioms H25821.mstep_ok
#print axioms H25821.halts_iff_zone
#print axioms H25821.zone_runs
#print axioms H25821.blank_runs_zone
#print axioms XS.swr_feed_ok
#print axioms XS.swr_feed_halt
#print axioms XS.swr_feed_reset
#print axioms XS.run_rep_pow
#print axioms XS.zone_period
#print axioms XS.never_of_quiet
#print axioms H25821.never_halts_of_quiet
#print axioms H25821.shield
#print axioms H25821.per_run
#print axioms H25821.blank_runs_shield
