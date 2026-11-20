import Bound

/-!
# 1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0RE---: no halt in the first 10^700 steps

The run of `Bound.lean` taken further; checked by `check_far.sh`, which loads compiled code for the evaluation
(about 40 minutes).
-/

namespace H72107

theorem bound_far : ∃ c, steps (10 ^ 700) init = some c :=
  bound_of_run (fuel := 10 ^ 15) (by native_decide)

end H72107
