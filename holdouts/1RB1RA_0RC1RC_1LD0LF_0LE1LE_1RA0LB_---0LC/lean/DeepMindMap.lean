import Machine

/-!
# A cited result: DeepMind's halts-iff map for 1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC

**Not proved in this repository.**  `deepmind_halts_iff` is an axiom: it states on this repository's definitions
what `BusyBeaver.M_1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_HHH0LC.isHalt_iff_acceleration` proves in google-deepmind/cryptids
(`BusyBeaver/BB6/M_1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_HHH0LC.lean`, commit 3647718, Lean v4.35.0-rc4 with Mathlib), namely
`IsHalt target ↔ CollatzHalts next start` for `target = (load_rle_machine% "1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC").toBB` from the blank tape:
the machine halts if and only if the orbit of `next` from `start` reaches `none`.

`DM.State`, `DM.start`, `DM.next` and the definitions they use are copied from that file, unchanged but for `ℕ`
written `Nat` (their docstrings describe the configuration each state stands for).  `tools/deepmind/orbits.sh` runs
this copy and DeepMind's own `next` for 120 steps from `start` and finds the same states.

The theorem was compiled here on 2026-11-17 (`tools/deepmind/`): it rests only on the axioms
propext, Classical.choice, Quot.sound, and its transition table was checked against this machine's.  The step from their
statement to this one is a translation, not a proof: their halting (Mathlib's Turing machine semantics, blank tape,
state A) is read as `TM.Halts trans (TM.blankCfg .A)`.  A proof here (as for `1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC`,
`lean/DMMap.lean`), or a bridge theorem between the two semantics, would turn the axiom into a theorem with the same
statement.  Written by `tools/deepmind/axioms.py`.
-/

set_option autoImplicit false

namespace H24009

namespace DM

inductive State where
  | D7 (a b : Nat)
  | D74 (a b : Nat)
  | D75 (a b c : Nat)
  | D76 (a b c : Nat)
  | D77 (a b c d : Nat)
  | D158 (a b c : Nat)
  | D160 (a b c : Nat)
  | D162 (a b c d : Nat)
  | D230 (a b c : Nat)
  | D231 (a b c d : Nat)
  | D294 (a b c : Nat)
  | D296 (a b c d : Nat)

def start : State := .D7 0 0

def next : State → Option State
  | .D7 0 b => some (.D77 0 0 0 (b + 1))
  | .D7 (a + 1) b => some (.D7 a (b + 1))
  | .D74 0 b => some (.D7 (b + 2) 0)
  | .D74 (a + 1) b => some (.D74 a (b + 1))
  | .D75 0 b 0 => some (.D158 (b + 1) 0 0)
  | .D75 0 b (c + 1) => some (.D160 (b + 1) 0 c)
  | .D75 (a + 1) b c => some (.D75 a (b + 1) c)
  | .D76 0 b 0 => some (.D75 0 0 (b + 2))
  | .D76 0 b (c + 1) => some (.D77 0 0 (b + 2) c)
  | .D76 (a + 1) b c => some (.D76 a (b + 1) c)
  | .D77 0 b 0 d => some (.D158 (b + 1) 0 (d + 1))
  | .D77 0 b (c + 1) d => some (.D162 (b + 1) 0 c d)
  | .D77 (a + 1) b c d => some (.D77 a (b + 1) c d)
  | .D158 0 b 0 => some (.D230 0 0 (b + 3))
  | .D158 0 b (c + 1) => some (.D231 0 0 (b + 2) c)
  | .D158 (a + 1) b c => some (.D158 a (b + 1) c)
  | .D160 0 b 0 => some (.D74 (b + 2) 0)
  | .D160 0 b (c + 1) => some (.D75 (b + 2) 0 c)
  | .D160 (a + 1) b c => some (.D160 a (b + 1) c)
  | .D162 0 b 0 d => some (.D76 (b + 2) 0 d)
  | .D162 0 b (c + 1) d => some (.D77 (b + 2) 0 c d)
  | .D162 (a + 1) b c d => some (.D162 a (b + 1) c d)
  | .D230 0 _ 0 => none
  | .D230 0 b 1 => some (.D74 (b + 1) 0)
  | .D230 0 b (c + 2) => some (.D294 (b + 1) 0 c)
  | .D230 (a + 1) b c => some (.D230 a (b + 1) c)
  | .D231 0 b 0 d => some (.D76 (b + 1) 0 d)
  | .D231 0 b (c + 1) d => some (.D296 (b + 1) 0 c d)
  | .D231 (a + 1) b c d => some (.D231 a (b + 1) c d)
  | .D294 0 b c => some (.D230 (b + 2) 0 c)
  | .D294 (a + 1) b c => some (.D294 a (b + 1) c)
  | .D296 0 b 0 d => some (.D158 (b + 2) 0 d)
  | .D296 0 b (c + 1) d => some (.D231 (b + 2) 0 c d)
  | .D296 (a + 1) b c d => some (.D296 a (b + 1) c d)

/-- `n` steps of `next` from `start`: DeepMind's `(Option.bind · next)^[n] (some start)` in `CollatzHalts`. -/
def orbit : Nat → Option State
  | 0 => some start
  | n + 1 => Option.bind (orbit n) next

end DM

/-- **Cited, not proved here**: `BusyBeaver.M_1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_HHH0LC.isHalt_iff_acceleration` (google-deepmind/cryptids, commit 3647718).  The machine halts
from blank tape if and only if the orbit of DeepMind's `next` stops. -/
axiom deepmind_halts_iff : HaltsFromBlank ↔ ∃ n, (DM.orbit n).isNone = true

end H24009
