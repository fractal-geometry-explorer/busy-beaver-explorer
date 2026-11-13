"""Write lean/Reach.lean: from blank tape to the main phases P 1 4 2 (step 173), P 1 14 2 (step 1225) and
P 1 46 2 (step 5625) by `native_decide`, and what `phase`, `main_to_turn` of lean/Phase.lean, lean/Levels.lean say
from there.  python3 holdouts/<M>/py/gen_reach.py"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "../../../tools/py"))
from bbtools.machine import Machine
M = "1RB0RA_1LC1RA_0LD1LD_0LE0LC_1LA0LF_---1LC"
m = Machine.parse(M)
B = lambda b: "true" if b == "1" else "false"
MAIN = [(173, 4, 2, "R0"), (1225, 14, 2, "R1"), (5625, 46, 2, "R2")]
tape, pos, st, n = {}, 0, 0, 0
body = []
for step, y, w, rn in MAIN:
    while n < step:
        wr, d, ns = m.table[st][tape.get(pos, 0)]
        tape[pos] = wr; pos += d; st = ns; n += 1
    assert st == 0 and pos < min(tape)
    s = "".join(str(tape.get(i, 0)) for i in range(pos, max(tape) + 1))
    want = "0" + "10" + "00" + "10" * y + "1100" + "1" * w + "0"
    assert s.startswith(want), s
    rest = s[len(want):]
    lst = "[" + ", ".join(B(b) for b in s) + "]"
    R = "blank"
    for b in reversed(rest):
        R = f"cons {B(b)} ({R})" if R != "blank" else f"cons {B(b)} blank"
    body.append(f"""/-- The rest of the tape at step {step}: `{rest}` then blank. -/
def {rn} : Tape := {R}

set_option maxRecDepth 100000 in
/-- After {step} steps the tape is `A>0 (10)^1 00 (10)^{y} 110 0 1^{w} 0` and `{rn}`, that is `P 1 {y} {w} {rn}`. -/
theorem reach_{step} : steps {step} init = some (P 1 {y} {w} {rn}) := by
  have h := blank_reaches trans (q := St.A) (n := {step}) (c := ⟨[], {lst}, .A⟩) (by native_decide)
  refine h.trans (congrArg some ?_)
  simp only [FCfg.toCfg, P, {rn}, rep_succ, rep_zero, app]
""")
    step_turn = step + sum(8 * (1 + 3 * i) + 4 * (y - i) + 26 for i in range(y)) + 14 * (1 + 3 * y) + 60
    body.append(f"""/-- That main phase ends at step {step_turn} as a wall of {6 * y + 12} ones (the head on the last of them), followed by
`1 0 1^{w + 2 * y + 4} 0` and `{rn}`. -/
theorem turn_{step} : steps {step_turn} init = some ⟨rep {6 * y + 11} [true] blank,
    cons true (cons true (cons false (rep {w + 2 * y + 4} [true] (cons false {rn})))), .A⟩ := by
  have h := steps_seq trans reach_{step} (main_to_turn {y} {w} {rn})
  exact steps_congr trans (by simp [pcost]) h
""")
out = f"""import Machine
import Blank
import Phase
import Levels

/-! From blank tape to the first three main phases, and each of them to its turn by `main_to_turn`.
Written by `py/gen_reach.py`. -/

namespace H154944

open TM

""" + "\n".join(body) + """
/-- The first phase: after 173 + 320 = 493 steps the tape is `P 13 0 10 R0`. -/
theorem phase_493 : steps 493 init = some (P 13 0 10 R0) := by
  have h := steps_seq trans reach_173 (phase 4 1 2 R0)
  exact steps_congr trans (by simp [pcost]) h

end H154944
"""
open(os.path.join(HERE, "../lean/Reach.lean"), "w").write(out)
print("wrote lean/Reach.lean")
