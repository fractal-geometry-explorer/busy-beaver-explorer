import XRace

/-!
# No lost race in the first 10^6 steps of `bstep`

Compiled evaluation (`native_decide`) of `racesOK`: from the first Q configuration (step 27), the first 10^6 steps
of the closed-form map `bstep` are defined and none of them is a lost race. With `not_halts_of_races` this does not
prove non-halting (the orbit is infinite); it is evidence that the race is always won.
-/

namespace H65140

theorem races_native : racesOK 1000000 start = true := by native_decide

end H65140
