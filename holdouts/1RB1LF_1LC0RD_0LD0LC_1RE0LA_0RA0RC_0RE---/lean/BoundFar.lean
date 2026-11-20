import Bound

/-!
# 1RB1LF_1LC0RD_0LD0LC_1RE0LA_0RA0RC_0RE---: no halt in the first 10^600 steps

The run of `Bound.lean` taken further; checked by `check_far.sh`, which loads compiled code for the evaluation
(about 30 minutes).
-/

namespace H69016

theorem bound_far : ∃ c, steps (10 ^ 600) init = some c :=
  bound_of_run (fuel := 10 ^ 15) (by native_decide)

end H69016
