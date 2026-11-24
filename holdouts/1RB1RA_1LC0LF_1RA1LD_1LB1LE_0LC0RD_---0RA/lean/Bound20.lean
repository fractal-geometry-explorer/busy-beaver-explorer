import Fast

/-! # Half of the run of `Bound.lean`: no halt in the first 1,048,576 visits

`c/wrun.c run 1048576` reports visit 1,048,576 at step 5,119,454,802,255; the faster model of `Fast.lean`, run by
compiled code, reaches it with step count 5,119,454,802,253 (two less, as in `Bound.lean`).  About 4.5 hours of one
core (16,097 s on 24 November 2026); check with `check_bound.sh Bound20.lean`. -/

namespace H129887

open TM

theorem blank_runs_1048576_visits : ∃ c, steps 5119454802253 init = some c :=
  blank_runs_of_fvrun 10000000000000 1048576 5119454802253 (by native_decide)

end H129887
