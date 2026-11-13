import Machine
import Rules

/-! From blank tape to a sweep start, and the next sweep by a rule of `Rules.lean`.  Written by `py/gen_reach.py`. -/

namespace H142609

open TM

set_option maxRecDepth 100000 in
/-- After 2,183 steps the head (state B) is on the blank cell right of the tape
`(10)^27 0 (10)^12 0 (10)^4 0 (10)^9 1`: counts 27, 12, 4, 10 (the shape of `sweep_E_EEO` with c = 2, y1 = 0, y2 = 4,
y3 = 11 and L blank). -/
theorem reach_2183 : steps 2183 init = some ⟨cons true (cons false (cons true (rep (2 + 2) [false, true, false, true]
    (cons false (rep (0 + 2) [false, true, false, true] (cons false (rep (4 + 2) [false, true, false, true]
    (cons false (cons false (cons true (rep (11 + 2) [false, true, false, true] blank))))))))))), blank, .B⟩ := by
  have h := blank_reaches trans (q := St.A) (n := 2183) (c := ⟨[true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true, false, true, false, true, false, true, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true], [], .B⟩) (by native_decide)
  refine h.trans (congrArg some ?_)
  simp only [FCfg.toCfg, rep_succ, rep_zero, app]

/-- The sweep that follows is `sweep_E_EEO`: counts (10, 4, 12, 27) become (11, 3, 14, 26), at step 2,367. -/
theorem sweep_2367 : ∃ c, steps 2367 init = some c := by
  have h := steps_seq trans reach_2183 (sweep_E_EEO 2 0 4 11 blank)
  exact ⟨_, steps_congr trans (by omega) h⟩

end H142609
