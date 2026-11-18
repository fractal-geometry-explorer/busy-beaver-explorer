import Machine

/-!
# A cited result: DeepMind's halts-iff map for 1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---

**Not proved in this repository.**  `deepmind_halts_iff` is an axiom: it states on this repository's definitions
what `BusyBeaver.M_1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RCHHH.isHalt_iff_acceleration` proves in google-deepmind/cryptids
(`BusyBeaver/BB6/M_1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RCHHH.lean`, commit 3647718, Lean v4.35.0-rc4 with Mathlib), namely
`IsHalt target ↔ CollatzHalts next start` for `target = (load_rle_machine% "1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---").toBB` from the blank tape:
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

namespace H9516

namespace DM

inductive State where
  /-- $C(m, k, b) := 0^\infty\,1^m\,(10)^k\,\mathrm{C}{>}\,1^b\,0^\infty$. -/
  | C (m k b : Nat)

def start : State := .C 0 0 2

def next : State → Option State
  | .C m k 0 => some (.C (m + 1) 0 (2 * k + 2))
  | .C 0 k 1 => some (.C (2 * k + 3) 0 2)
  | .C 0 k (b + 2) => some (.C (2 * k + 2) 1 b)
  | .C 1 0 (b + 1) => some (.C 0 0 (b + 3))
  | .C 1 (k + 1) 1 => some (.C (2 * k + 7) 0 2)
  | .C 1 (k + 1) (b + 2) => some (.C (2 * k + 6) 1 b)
  | .C 2 0 1 => some (.C 0 1 0)
  | .C 2 0 (_ + 2) => none
  | .C 2 1 (b + 1) => some (.C 0 1 (b + 1))
  | .C 2 (k + 2) 1 => some (.C (2 * k + 7) 0 2)
  | .C 2 (k + 2) (b + 2) => some (.C (2 * k + 6) 1 b)
  | .C (m + 3) k (b + 1) => some (.C m (k + 2) b)

/-- `n` steps of `next` from `start`: DeepMind's `(Option.bind · next)^[n] (some start)` in `CollatzHalts`. -/
def orbit : Nat → Option State
  | 0 => some start
  | n + 1 => Option.bind (orbit n) next

end DM

/-- **Cited, not proved here**: `BusyBeaver.M_1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RCHHH.isHalt_iff_acceleration` (google-deepmind/cryptids, commit 3647718).  The machine halts
from blank tape if and only if the orbit of DeepMind's `next` stops. -/
axiom deepmind_halts_iff : HaltsFromBlank ↔ ∃ n, (DM.orbit n).isNone = true

end H9516
