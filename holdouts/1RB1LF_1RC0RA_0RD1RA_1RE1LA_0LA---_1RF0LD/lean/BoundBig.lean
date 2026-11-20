import Bound

/-!
# 1RB1LF_1RC0RA_0RD1RA_1RE1LA_0LA---_1RF0LD: no halt in the first 10^300 steps

The run of `Bound.lean` taken further; checked by `check_big.sh`, which loads compiled code for the evaluation.
-/

namespace H180268

theorem bound_big : ∃ c, steps (10 ^ 300) init = some c :=
  bound_of_run (fuel := 10 ^ 15) (by native_decide)

end H180268
