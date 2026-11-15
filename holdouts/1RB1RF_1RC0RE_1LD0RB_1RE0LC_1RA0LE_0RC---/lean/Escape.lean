import Machine

/-!
# 1RB1RF_1RC0RE_1LD0RB_1RE0LC_1RA0LE_0RC---: a tape of the block form that halts

The run from blank tape keeps the form "blocks a^k (a = 01) separated by b = 00110, with single cursor cells 0 or 1";
cursors can come to stand next to each other.  That form alone does not exclude a halt: when three cursor cells 1
stand together (`1 1 1`, four 1s on the tape after the 1 of an a) and the next cursor, a 0, arrives directly right
of them, the machine halts.  The theorem below is one such tape:

    0^inf 1 a b a 0 a 1 1 1 0 a^22 0 B> 0^inf      halts after 213 steps

It is reached in 13 visits of the right end from `1 a b a 0 a 1 1 a b 0 b a 0 B>` (the tape of a cursor 0 stopped in
the middle of crossing a separator, `0 a 1 1 a b`, with a second cursor arriving), see the README.  This is not a
statement about the run from blank tape, in which no such tape has been seen: it shows what an invariant has to
exclude.  The run is evaluated on the list simulator of `tools/lean/TM/Fin.lean` by Lean's kernel.
-/

namespace H75404

open TM

/-- `1 a b a 0 a 1 1 1 0 a^22 0`, nearest cell first, left of the head. -/
def escLeft : List Bool := [false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, false, true, false, true]

/-- The start: state B on the blank cell right of the word. -/
def escStart : FCfg St := ⟨escLeft, [], .B⟩

/-- After 213 steps the machine is at its halting transition. -/
theorem esc_run : (fsteps 213 escStart).map (fun c => (fstep c).isNone) = some true := by
  decide +kernel

/-- The tape `1 a b a 0 a 1 1 1 0 a^22 0 B>` of the block form halts. -/
theorem esc_halts : Halts trans escStart.toCfg := by
  have h := esc_run
  cases hc : fsteps 213 escStart with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some c =>
    rw [hc] at h
    have hn : fstep c = none := by
      simpa using h
    refine ⟨213, c.toCfg, ?_, ?_⟩
    · show TM.steps trans 213 escStart.toCfg = some c.toCfg
      rw [FCfg.steps_eq trans]; show (fsteps 213 escStart).map FCfg.toCfg = _; rw [hc]; rfl
    · rw [FCfg.step_eq trans]; show (fstep c).map FCfg.toCfg = none; rw [hn]; rfl

end H75404
