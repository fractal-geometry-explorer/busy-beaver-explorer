import Machine

/-!
# A cited result: DeepMind's halts-iff map for 1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE

**Not proved in this repository.**  `deepmind_halts_iff` is an axiom: it states on this repository's definitions
what `BusyBeaver.M_1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_HHH1RE.isHalt_iff_acceleration` proves in google-deepmind/cryptids
(`BusyBeaver/BB6/M_1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_HHH1RE.lean`, commit 3647718, Lean v4.35.0-rc4 with Mathlib), namely
`IsHalt target ↔ CollatzHalts next start` for `target = (load_rle_machine% "1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE").toBB` from the blank tape:
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

namespace H89542

namespace DM

inductive State where
  /-- $A(a, c, d) := 0^\infty\,1^a\,\mathrm{A}{>}\,(10)^c\,1^{d+1}\,0^\infty$. -/
  | A (a c d : Nat)
  /-- $\mathrm{Run}(a) := 0^\infty\,1^a\,\mathrm{D}{>}\,0^\infty$. -/
  | Run (a : Nat)
  deriving DecidableEq, Repr

def start : State := .A 2 0 1

def next : State → Option State
  | .Run a => some (.Run (a + 1))
  | .A (a + 2) c d => some (.A a (c + 1) d)
  | .A 0 _ 0 => none
  | .A 0 c 1 => some (.A (2 * c + 1) 0 0)
  | .A 0 c (d + 2) => some (.A (2 * c + 1) 1 d)
  | .A 1 c 0 =>
      if c % 2 = 0 then some (.Run 1) else some (.A 2 0 (3 * c + 4))
  | .A 1 c 1 =>
      if c % 2 = 0 then some (.A 2 0 (3 * c + 6)) else some (.A (3 * c + 5) 0 0)
  | .A 1 c (d + 2) =>
      if c % 2 = 0 then some (.A (3 * c + 7) 0 d) else some (.A (3 * c + 5) 0 (d + 1))

/-- `n` steps of `next` from `start`: DeepMind's `(Option.bind · next)^[n] (some start)` in `CollatzHalts`. -/
def orbit : Nat → Option State
  | 0 => some start
  | n + 1 => Option.bind (orbit n) next

end DM

/-- **Cited, not proved here**: `BusyBeaver.M_1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_HHH1RE.isHalt_iff_acceleration` (google-deepmind/cryptids, commit 3647718).  The machine halts
from blank tape if and only if the orbit of DeepMind's `next` stops. -/
axiom deepmind_halts_iff : HaltsFromBlank ↔ ∃ n, (DM.orbit n).isNone = true

end H89542
