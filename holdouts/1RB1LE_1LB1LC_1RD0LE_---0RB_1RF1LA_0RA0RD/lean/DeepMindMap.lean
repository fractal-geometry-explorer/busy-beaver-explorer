import Machine

/-!
# A cited result: DeepMind's halts-iff map for 1RB1LE_1LB1LC_1RD0LE_---0RB_1RF1LA_0RA0RD

**Not proved in this repository.**  `deepmind_halts_iff` is an axiom: it states on this repository's definitions
what `BusyBeaver.M_1RB1LE_1LB1LC_1RD0LE_HHH0RB_1RF1LA_0RA0RD.isHalt_iff_acceleration` proves in google-deepmind/cryptids
(`BusyBeaver/BB6/M_1RB1LE_1LB1LC_1RD0LE_HHH0RB_1RF1LA_0RA0RD.lean`, commit 3647718, Lean v4.35.0-rc4 with Mathlib), namely
`IsHalt target ↔ CollatzHalts next start` for `target = (load_rle_machine% "1RB1LE_1LB1LC_1RD0LE_---0RB_1RF1LA_0RA0RD").toBB` from the blank tape:
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

namespace H25239

namespace DM

inductive State where
  /-- Canonical hub configuration
  $E(q, a, b, c) := 0^\infty\,\mathrm{E}{>}\,0\,0^q\,1^a\,0\,1^b\,0\,1^c\,0^\infty$
  with $q \in \{0, 1\}$. -/
  | E (q : Bool) (a b c : Nat)
  /-- Even-block right-sweep configuration
  $F(d, 2k, b, c) := 0^\infty\,1^{d+1}\,\mathrm{F}{>}\,1^{2k}\,0\,1^b\,0\,1^c\,0^\infty$. -/
  | F_even (d k b c : Nat)

def start : State := .E true 3 0 0

def mkE (m b c : Nat) : State :=
  .E (decide (m % 2 = 1)) m b c

def enterF_d0 (a b c : Nat) : Option State :=
  if a % 2 = 0 then
    some (.F_even 0 (a / 2) b c)
  else if a = 1 then
    none
  else if a = 3 then
    some (mkE (b + 2) (c + 3) 0)
  else
    none

def enterF_d1 (a b c : Nat) : Option State :=
  if a % 2 = 0 then
    some (.F_even 1 (a / 2) b c)
  else if a = 1 then
    none
  else if a = 3 then
    some (mkE (b + 3) (c + 3) 0)
  else
    some (.E true (a - 2) (b + 6) c)

def enterF_c0 (d a b : Nat) : Option State :=
  if a % 2 = 0 then
    some (.F_even d (a / 2) b 0)
  else if a = 1 then
    none
  else if a = 3 then
    some (mkE (d + b + 2) 3 0)
  else
    some (mkE (d + 1) (a - 4) (b + 3))

def next : State → Option State
  | .E false a b c => enterF_d0 a b c
  | .E true 0 0 0 => none
  | .E true 0 0 (c + 1) => some (mkE (c + 2) 3 0)
  | .E true 0 (b + 1) c => enterF_c0 2 (b + 1) c
  | .E true (a + 1) b c => enterF_d1 (a + 1) b c
  | .F_even d 0 0 0 => some (mkE (d + 1) 3 0)
  | .F_even d 0 0 (c + 1) => some (.F_even (d + 1) 0 (c + 1) 0)
  | .F_even d 0 (b + 1) c => enterF_c0 (d + 1) (b + 1) c
  | .F_even 0 1 b c => some (mkE (b + 2) (c + 3) 0)
  | .F_even 1 1 b c => some (.E true (b + 4) c 0)
  | .F_even (d + 2) 1 b c => some (mkE (d + 1) (b + 4) c)
  | .F_even d (k + 2) b c => some (.F_even (d + 1) k (b + 3) c)

/-- `n` steps of `next` from `start`: DeepMind's `(Option.bind · next)^[n] (some start)` in `CollatzHalts`. -/
def orbit : Nat → Option State
  | 0 => some start
  | n + 1 => Option.bind (orbit n) next

end DM

/-- **Cited, not proved here**: `BusyBeaver.M_1RB1LE_1LB1LC_1RD0LE_HHH0RB_1RF1LA_0RA0RD.isHalt_iff_acceleration` (google-deepmind/cryptids, commit 3647718).  The machine halts
from blank tape if and only if the orbit of DeepMind's `next` stops. -/
axiom deepmind_halts_iff : HaltsFromBlank ↔ ∃ n, (DM.orbit n).isNone = true

end H25239
