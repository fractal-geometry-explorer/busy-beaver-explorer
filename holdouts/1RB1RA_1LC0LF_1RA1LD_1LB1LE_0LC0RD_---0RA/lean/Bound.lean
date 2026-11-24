import Fast

/-! # The run of `c/wrun.c`, checked: no halt in the first 2,097,152 visits

`c/wrun.c run 2097152` reports visit 2,097,152 at step 13,274,338,602,371 (its step count is two steps past the
state `RET(1, v)` on the empty stack).  The faster model of `Fast.lean`, run by compiled code (`native_decide`),
reaches that visit with step count 13,274,338,602,369 = 13,274,338,602,371 − 2, so the machine runs that many steps
from blank tape without halting.  About 15.5 hours of one core (55,983 s on 24 November 2026); check with `check_bound.sh`. -/

namespace H129887

open TM

theorem blank_runs_2097152_visits : ∃ c, steps 13274338602369 init = some c :=
  blank_runs_of_fvrun 10000000000000 2097152 13274338602369 (by native_decide)

end H129887
