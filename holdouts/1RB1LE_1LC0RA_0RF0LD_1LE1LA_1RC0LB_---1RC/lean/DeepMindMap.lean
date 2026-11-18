import Machine

/-!
# A cited result: DeepMind's halts-iff map for 1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC

**Not proved in this repository.**  `deepmind_halts_iff` is an axiom: it states on this repository's definitions
what `BusyBeaver.M_1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_HHH1RC.isHalt_iff_acceleration` proves in google-deepmind/cryptids
(`BusyBeaver/BB6/M_1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_HHH1RC.lean`, commit 3647718, Lean v4.35.0-rc4 with Mathlib), namely
`IsHalt target ↔ CollatzHalts next start` for `target = (load_rle_machine% "1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC").toBB` from the blank tape:
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

namespace H113170

namespace DM

inductive State where
  /-- $A(a, b) := 0^\infty\,{<}\mathrm{C}\,(10)^a\,110\,(10)^b\,0^\infty$. -/
  | A (a b : Nat)
  /-- $B(a, b, c) := 0^\infty\,{<}\mathrm{C}\,(10)^a\,110\,(10)^b\,110\,(1010)^c\,0^\infty$. -/
  | B (a b c : Nat)

def start : State := .A 2 0

def next : State → Option State
  | .A a b =>
    if a < b then
      some (.A (2 * a + 2) (b - a - 1))
    else if a = b then
      none
    else if (a - b - 1) % 2 = 0 then
      some (.A (2 * ((a - b - 1) / 2) + 2) (2 * b + 2))
    else
      some (.B 2 (2 * ((a - b - 1) / 2) + 1) (b + 1))
  | .B a b c =>
    if a < b then
      some (.B (2 * a + 2) (b - a - 1) c)
    else if a = b then
      some (.A 2 (4 * a + 2 * c + 6))
    else
      some (.A 2 (2 * a + 2 * c + 2))

/-- `n` steps of `next` from `start`: DeepMind's `(Option.bind · next)^[n] (some start)` in `CollatzHalts`. -/
def orbit : Nat → Option State
  | 0 => some start
  | n + 1 => Option.bind (orbit n) next

end DM

/-- **Cited, not proved here**: `BusyBeaver.M_1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_HHH1RC.isHalt_iff_acceleration` (google-deepmind/cryptids, commit 3647718).  The machine halts
from blank tape if and only if the orbit of DeepMind's `next` stops. -/
axiom deepmind_halts_iff : HaltsFromBlank ↔ ∃ n, (DM.orbit n).isNone = true

end H113170
