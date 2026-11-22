import Race

/-!
# The list machine from this machine's blank tape

`End.lean` (ported) turns every right turn of this table into a state of the list machine `astep`.  This machine
is that table started in its own state A (state E of 1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF), so its run
reaches the list machine at a different first right turn: step 48, A on the last 1, zone `b a b a a a` (nearest
letter first, `b = true`), prefix 1.  Tape at that turn: `1 11 11 11 10 11 10 | 1`.
-/

namespace H58953
open TM

/-- The first right turn from blank tape, step 48: A on the last 1, zone `b a b a a a`, prefix 1. -/
theorem start : steps 48 init = some (cfg (.EO [true, false, true, false, false, false] none true)) := by
  rfl

/-- **The holdout as a list question.**  If the list machine never fails from the first right turn, the machine
never halts from blank tape. -/
theorem not_halts_of_arun
    (h : ∀ k, (arun k (.EO [true, false, true, false, false, false] none true)).isSome) : ¬ HaltsFromBlank := by
  apply not_halts_of_forall
  apply forall_of_unbounded trans (fun m => ∃ c', steps m init = some c')
  · intro n
    obtain ⟨b, m, _, hm, hs⟩ := arun_steps _ h n
    exact ⟨48 + m, by omega, _, steps_seq trans start hs⟩
  · intro m hm; exact hm

end H58953
