import Blank
import Rules
import ZoneRun
import ZoneCascade
import WindowRun

/-! What the main theorems rest on: the kernel ones only on `propext`, `Classical.choice`, `Quot.sound`; the
`native_decide` ones also on the auxiliary axiom that `native_decide` adds. -/

#print axioms H117020.mstep_sound
#print axioms H117020.orbT_sound
#print axioms H117020.halts_iff
#print axioms XS.zone_step
#print axioms XS.swr_split
#print axioms XS.swr_append_ok
#print axioms H117020.mstep_ok
#print axioms H117020.halts_iff_zone
#print axioms H117020.zone_runs
#print axioms H117020.blank_runs_zone
#print axioms XS.swr_feed_ok
#print axioms XS.swr_feed_halt
#print axioms XS.swr_feed_reset
#print axioms XS.run_rep_pow
#print axioms XS.zone_period
#print axioms XS.never_of_quiet
#print axioms H117020.never_halts_of_quiet
#print axioms XS.wfold_run
#print axioms XS.window_of_check
#print axioms H117020.window_runs
#print axioms H117020.blank_runs_window
