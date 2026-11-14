import Law
import VisitRun

/-!
# 1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RE--- halts

`Law.lean` reduces halting from blank tape to one evaluation of the checker: `check 161210 [true] = true` (after
161,210 rounds the next round halts).  `VisitRun.lean` proves that evaluation in ten segments, each by
`native_decide` with the checker compiled to native code (`check_halt.sh`).  So this theorem depends on
`Lean.ofReduceBool` (trust in the Lean compiler, for those evaluations) besides the three standard axioms;
everything else is kernel-checked.
-/

namespace H32161

open TM VisitLaw

/-- The machine halts from blank tape. -/
theorem halts_from_blank : HaltsFromBlank := halts_of_check_blank 161210 VisitLaw.Run.check_run

#print axioms halts_from_blank

end H32161
