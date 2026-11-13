import Machine

/-!
# 1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF: block configurations of the run from blank tape

A block configuration `[b₁, …, bₖ]` is `0^∞ 1^b₁ 0 1^b₂ 0 … 0 1^bₖ C>0 0^∞` (see README.md).  The run from blank
tape passes through `[4, 3, 9]` at step 204, `[9, 12]` at step 420, `[4, 18, 28]` at step 99,072 and `[4, 17, 27, 3]`
at step 197,318; from there the rounds of `Rules.lean` (and the odd round law beyond them) take it to
`[4, 17, 27, 57]` at step 3,221,422,604.  Generated with `py/fcfg.py`.
-/

namespace H168016

open TM

/-- The configuration after 204 steps from blank tape. -/
theorem blank_at_204 :
    steps 204 init = some (FCfg.toCfg ⟨[true, true, true, true, true, true, true, true, true, false, true, true, true, false, true, true, true, true, false],
      [], .C⟩) :=
  blank_reaches trans (by decide +kernel)

/-- The configuration after 420 steps from blank tape. -/
theorem blank_at_420 :
    steps 420 init = some (FCfg.toCfg ⟨[true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, false],
      [], .C⟩) :=
  blank_reaches trans (by decide +kernel)

/-- The configuration after 99,072 steps from blank tape. -/
theorem blank_at_99072 :
    steps 99072 init = some (FCfg.toCfg ⟨[true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, false],
      [], .C⟩) :=
  blank_reaches trans (by native_decide)

/-- The configuration after 197,318 steps from blank tape. -/
theorem blank_at_197318 :
    steps 197318 init = some (FCfg.toCfg ⟨[true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, false],
      [], .C⟩) :=
  blank_reaches trans (by native_decide)

end H168016
