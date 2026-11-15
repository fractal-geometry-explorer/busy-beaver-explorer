import Machine

/-! # A word over 110 and 111 on which the machine halts

At every visit of the left end in the run from blank tape (head in B on the blank cell left of the tape) the tape
is a word over the tokens b = 110 and c = 111.  An earlier conjecture said that the visit on *every* such word leads
to a visit on such a word again, which would have meant that the machine never halts.  It is false: on the word
`b c c c b b b b c c b b b b b b c b c` (19 tokens; no shorter word halts, by `c/wrun.c enum`) the machine halts
on its 6,323rd step.  The configuration is not one of the run from blank tape, so this says nothing about that run
except that an argument for it has to use more than "the tape is a word". -/

namespace H129887

open TM

/-- The cells of a word: `false` is the token b = 110, `true` the token c = 111. -/
def cells : List Bool → List Bool
  | [] => []
  | x :: w => true :: true :: x :: cells w

/-- The visit on a word: blank tape on the left, the head in B on a blank cell, the word right of it. -/
def visit (w : List Bool) : FCfg St := ⟨[], false :: cells w, .B⟩

/-- `b c c c b b b b c c b b b b b b c b c`. -/
def haltingWord : List Bool :=
  [false, true, true, true, false, false, false, false, true, true, false, false, false, false, false, false,
   true, false, true]

/-- The visit on `haltingWord` halts: 6,322 transitions, then a configuration with no transition (the halt is the
6,323rd step in bbchallenge's count).  Evaluated by Lean's kernel on the list simulator. -/
theorem haltingWord_halts :
    ∃ c, steps 6322 (visit haltingWord).toCfg = some c ∧ step c = none := by
  have h : ((fsteps 6322 (visit haltingWord)).bind fun c => some (fstep c)) = some none := by decide +kernel
  cases e : fsteps 6322 (visit haltingWord) with
  | none => rw [e] at h; cases h
  | some c =>
    rw [e] at h
    refine ⟨c.toCfg, ?_, ?_⟩
    · show TM.steps trans 6322 (visit haltingWord).toCfg = some c.toCfg
      have e' : TM.fsteps trans 6322 (visit haltingWord) = some c := e
      rw [FCfg.steps_eq, e']; rfl
    · show TM.step trans c.toCfg = none
      have h' : TM.fstep trans c = none := by simpa using h
      rw [FCfg.step_eq, h']; rfl

/-- So "the tape is a word over b and c" is not an invariant that excludes a halt. -/
theorem word_can_halt : ∃ w : List Bool, Halts trans (visit w).toCfg :=
  ⟨haltingWord, by
    obtain ⟨c, h₁, h₂⟩ := haltingWord_halts
    exact ⟨6322, c, h₁, h₂⟩⟩

end H129887
