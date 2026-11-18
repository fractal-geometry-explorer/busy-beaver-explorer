import Machine

/-!
# A cited result: DeepMind's halts-iff map for 1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LF---_0LA1LA

**Not proved in this repository.**  `deepmind_halts_iff` is an axiom: it states on this repository's definitions
what `BusyBeaver.M_1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LFHHH_0LA1LA.isHalt_iff_acceleration` proves in google-deepmind/cryptids
(`BusyBeaver/BB6/M_1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LFHHH_0LA1LA.lean`, commit 3647718, Lean v4.35.0-rc4 with Mathlib), namely
`IsHalt target ↔ CollatzHalts next start` for `target = (load_rle_machine% "1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LF---_0LA1LA").toBB` from the blank tape:
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

namespace H12891

namespace DM

inductive State where
  /-- $P(b, k, c) := 0^\infty\,1111\,0^b\,\mathrm{F}{>}\,(111)^k\,0\,1^c\,011\,0^\infty$. -/
  | P (b k c : Nat)

def start : State := .P 4 0 11

def next : State → Option State
  | .P 0 k c => some (.P (3 * k + 3) 0 (c + 2))
  | .P 1 k 0 => if k = 2 then some (.P 7 2 18) else none
  | .P 1 k 1 => if k = 1 then some (.P 7 2 18) else none
  | .P 1 k (c + 2) => some (.P 0 (k + 1) c)
  | .P (b + 2) k 0 => some (.P b 0 (3 * k + 5))
  | .P (b + 2) k 1 => some (.P b 0 (3 * k + 8))
  | .P (b + 2) k (c + 2) => some (.P (b + 1) (k + 1) c)

/-- `n` steps of `next` from `start`: DeepMind's `(Option.bind · next)^[n] (some start)` in `CollatzHalts`. -/
def orbit : Nat → Option State
  | 0 => some start
  | n + 1 => Option.bind (orbit n) next

end DM

/-- **Cited, not proved here**: `BusyBeaver.M_1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LFHHH_0LA1LA.isHalt_iff_acceleration` (google-deepmind/cryptids, commit 3647718).  The machine halts
from blank tape if and only if the orbit of DeepMind's `next` stops. -/
axiom deepmind_halts_iff : HaltsFromBlank ↔ ∃ n, (DM.orbit n).isNone = true

end H12891
