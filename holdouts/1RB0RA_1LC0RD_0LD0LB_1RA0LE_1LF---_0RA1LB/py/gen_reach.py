"""Write lean/Reach.lean: from blank tape to the first transfer phase, and five cycles of it.
python3 holdouts/<M>/py/gen_reach.py"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "../../../tools/py"))
from bbtools.machine import Machine
M = "1RB0RA_1LC0RD_0LD0LB_1RA0LE_1LF---_0RA1LB"
m = Machine.parse(M)
N = 16718
tape, pos, st = {}, 0, 0
for n in range(N):
    w, d, ns = m.table[st][tape.get(pos, 0)]
    tape[pos] = w; pos += d; st = ns
assert st == 2 and pos <= min(tape)
right = [tape.get(i, 0) for i in range(pos, max(tape) + 1)]
B = lambda b: "true" if b else "false"
lst = "[" + ", ".join(B(b) for b in right) + "]"
out = f"""import Machine
import Cycle

/-! From blank tape to the first transfer phase.  Written by `py/gen_reach.py`. -/

namespace H65987

open TM

/-- The rest of the tape right of the marker at step 16,718: `(10)^15 0 (10)^3 1`, then blank. -/
def R0 : Tape := rep 15 [true, false] (cons false (rep 3 [true, false] (cons true blank)))

set_option maxRecDepth 100000 in
/-- After 16,718 steps the tape is `G (10)^64 111 0 (10)^15 0 (10)^3 1` with the head (C) on the left end. -/
theorem reach_16718 : steps {N} init = some (cyc 32 R0) := by
  have h := blank_reaches trans (q := St.A) (n := {N}) (c := ⟨[], {lst}, .C⟩) (by native_decide)
  refine h.trans (congrArg some ?_)
  simp only [FCfg.toCfg, cyc, gad, R0, rep_succ, rep_zero, app]

/-- Five cycles later (step 29,508, as the simulator says) the marker has moved 60 pairs left:
`G (10)^4 111 0 (10)^90 0 (10)^3 1`. -/
theorem phase_end_29508 : steps 29508 init = some (cyc 2 (rep 75 [true, false] R0)) := by
  have h := steps_seq trans reach_16718 (cycles 5 2 R0)
  exact steps_congr trans (by simp [ccost]) h

end H65987
"""
open(os.path.join(HERE, "../lean/Reach.lean"), "w").write(out)
print("wrote lean/Reach.lean")
