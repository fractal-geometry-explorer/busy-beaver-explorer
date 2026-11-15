import Run

/-!
# 1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE halts

The simulator of `Sim.lean` and `Run.lean`, started on blank tape, meets the halting transition within 10^8 rounds
(about 88.9 million: 68.6 million single transitions, 13.4 million runs crossed, 6.7 million copies unpacked, and
86,734 jumps of up to 2^214 visits each).  The evaluation is `native_decide`, so `halts` trusts Lean's compiler besides the kernel; everything
else (that each round follows the machine, `run_sound`) is proved.
-/

namespace H172044

open TM

/-- The simulator reaches the halting transition (compiled evaluation). -/
theorem run_halts : run 100000000 start = true := by native_decide

/-- **The machine halts from blank tape.** -/
theorem halts : HaltsFromBlank := by
  have h := run_sound _ start run_halts
  rw [sem_start] at h
  exact h

end H172044

/-! What the results rest on: `propext`, `Classical.choice` and `Quot.sound` are the standard axioms; an axiom named
after `native_decide` (`Lean.ofReduceBool`, `Lean.trustCompiler`) means the theorem also trusts Lean's compiler. -/

#print axioms H172044.visit
#print axioms H172044.jump
#print axioms H172044.run_sound
#print axioms H172044.halts
