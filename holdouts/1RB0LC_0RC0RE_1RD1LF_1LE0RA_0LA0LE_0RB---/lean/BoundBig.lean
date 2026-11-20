import Bound

/-!
# 1RB0LC_0RC0RE_1RD1LF_1LE0RA_0LA0LE_0RB---: no halt in the first 10^100 steps

The run of `Bound.lean` taken further; checked by `check_big.sh`, which loads compiled code for the evaluation.
-/

namespace H123261

theorem bound_big : ∃ c, steps (10 ^ 100) init = some c :=
  bound_of_run (fuel := 10 ^ 15) (by native_decide)

end H123261
