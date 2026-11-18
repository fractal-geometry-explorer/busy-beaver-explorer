import Machine

/-!
# A cited result: DeepMind's proof that 1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RD--- halts

**Not proved in this repository.**  `deepmind_halts` is an axiom: it states on this repository's definitions what
`BusyBeaver.M_1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RDHHH.is_halt` proves in google-deepmind/cryptids
(`BusyBeaver/BB6/M_1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RDHHH.lean`, commit 3647718, Lean v4.35.0-rc4 with Mathlib), namely
`IsHalt target` for `target = (load_rle_machine% "1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RD---").toBB` from the blank tape.

That theorem was compiled here on 2026-11-17 (`tools/deepmind/`): it rests only on the axioms
propext, Classical.choice, Quot.sound, and its transition table was checked against this machine's.  The step from their
statement to this one is a translation, not a proof: their halting (Mathlib's Turing machine semantics, blank tape,
state A) is read as `TM.Halts trans (TM.blankCfg .A)`.  A proof here, or a bridge theorem between the two
semantics, would turn this axiom into a theorem with the same statement.  `#print axioms` lists `deepmind_halts` for every
theorem that uses it.  Written by `tools/deepmind/axioms.py`.
-/

namespace H124060

/-- **Cited, not proved here**: `BusyBeaver.M_1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RDHHH.is_halt` (google-deepmind/cryptids, commit 3647718). -/
axiom deepmind_halts : HaltsFromBlank

end H124060
