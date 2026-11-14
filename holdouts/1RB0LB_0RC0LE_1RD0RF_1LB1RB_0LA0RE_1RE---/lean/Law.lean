import Visit
import VisitCheck

/-!
# The visit law of 1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RE---, and what the checker has to find

The machine's two forms of visit (`Visit.lean`) obey the abstract visit law (`VisitLaw.lean`) and a round of the
machine is one visit, so the machine halts from blank tape as soon as the checker of `VisitCheck.lean` accepts:
`check k [true] = true` for some `k`.  Everything in this file is checked by the kernel alone.
-/

namespace H32161

open TM VisitLaw

/-- The machine's visits obey the visit law. -/
theorem law : Law V W VH WH where
  v0 := fun _ => V_0
  vh := V_100
  vg := V_110
  vl := V_1010
  w0 := fun _ => W_0
  wh := W_100
  wl := W_1010
  vx := fun _ => V_1011_halts
  vhh := V_100_halts_1
  vgh := V_110_halts_1
  vl1 := V_1010_halts_1
  vl2 := V_1010_halts_2
  wx := fun _ => W_1011_halts
  whh := W_100_halts_1
  wl1 := W_1010_halts_1
  wl2 := W_1010_halts_2

/-- If the checker accepts `k` rounds and a halting round after them, the machine halts from blank tape. -/
theorem halts_of_check_blank (k : Nat) (h : check k [true] = true) : HaltsFromBlank :=
  halts_of_check trans law LE init round round_halts [true] ⟨_, start⟩ k h

end H32161
