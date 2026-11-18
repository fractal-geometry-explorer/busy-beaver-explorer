import Machine

/-!
# A cited result: DeepMind's halts-iff map for 1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA

**Not proved in this repository.**  `deepmind_halts_iff` is an axiom: it states on this repository's definitions
what `BusyBeaver.M_1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_HHH1RA.isHalt_iff_acceleration` proves in google-deepmind/cryptids
(`BusyBeaver/BB6/M_1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_HHH1RA.lean`, commit 3647718, Lean v4.35.0-rc4 with Mathlib), namely
`IsHalt target ↔ CollatzHalts next start` for `target = (load_rle_machine% "1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA").toBB` from the blank tape:
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

namespace H13743

namespace DM

inductive State where
  /-- $E(a, k, c) := 0^\infty\,1^a\,\mathrm{A}{>}\,0\,(11)^k\,0\,1^c\,0^\infty$. -/
  | E (a k c : Nat)
  /-- $M_1(a, k, d+1) := 0^\infty\,1^a\,0\,(11)^k\,1\,0\,\mathrm{C}{>}\,1^{d+1}\,0^\infty$. -/
  | M_1 (a k d : Nat)
  /-- $M_0(n, z) := 0^\infty\,1^n\,1\,0\,\mathrm{C}{>}\,1^z\,0^\infty$. -/
  | M_0 (n z : Nat)

def start : State := .E 3 0 2

def next : State → Option State
  | .E a 0 c => some (.M_0 a c)
  | .E a 1 c =>
    if c % 2 = 0 then some (.E (a + 3) (c / 2) 0)
    else if c = 1 then none
    else some (.M_0 (a + 5) (c - 3))
  | .E a (k + 2) 0 => some (.M_0 (a + 2) (2 * k + 1))
  | .E a (k + 2) (d + 1) => some (.M_1 (a + 3) k d)
  | .M_1 a k d =>
    if d % 2 = 0 then some (.E (a + 3) k (d + 1))
    else if d = 1 then some (.E a 1 (2 * k + 2))
    else some (.E (a + 3) (k + 1) (d - 1))
  | .M_0 n 0 => some (.E 3 0 (n + 2))
  | .M_0 n (d + 1) =>
    if d % 2 = 0 then
      if n % 2 = 0 then some (.E 3 (n / 2) (d + 1))
      else some (.E 4 (n / 2 + 1) (d + 1))
    else if d = 1 then
      if n % 2 = 0 then some (.E 0 1 (n + 2))
      else some (.E 1 1 (n + 3))
    else
      if n % 2 = 0 then some (.E 3 (n / 2 + 1) (d - 1))
      else some (.E 4 (n / 2 + 2) (d - 1))

/-- `n` steps of `next` from `start`: DeepMind's `(Option.bind · next)^[n] (some start)` in `CollatzHalts`. -/
def orbit : Nat → Option State
  | 0 => some start
  | n + 1 => Option.bind (orbit n) next

end DM

/-- **Cited, not proved here**: `BusyBeaver.M_1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_HHH1RA.isHalt_iff_acceleration` (google-deepmind/cryptids, commit 3647718).  The machine halts
from blank tape if and only if the orbit of DeepMind's `next` stops. -/
axiom deepmind_halts_iff : HaltsFromBlank ↔ ∃ n, (DM.orbit n).isNone = true

end H13743
