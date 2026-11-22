import Machine
import TM.RSim

/-!
# 1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD1RF: no halt in the first 10^8 steps, by the checked accelerated simulator

`TM/RSim.lean` is rsim (the accelerated simulator of `c/rsim_fast.cpp`) rebuilt so that every move is proved,
including its trip-level jumps: each jump is checked by running one period symbolically, with the counts of the runs
as linear forms. This file runs it from blank tape far enough for continuous integration; `RSimLong.lean` (checked
by `check_long.sh`, with compiled code loaded) runs it much further.
-/

namespace H83242

open TM TM.RS

deriving instance Hashable for St

/-- No halt in the first 10^8 steps (`native_decide` on the checked simulator). -/
theorem rsim_1e8 : ∃ c, TM.steps trans 100000000 (TM.blankCfg .A) = some c :=
  run_ok trans .A 100000000 1000000000 (by native_decide)

end H83242
