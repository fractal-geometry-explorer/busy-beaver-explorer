import Machine

/-!
# A cited result: DeepMind's halts-iff map for 1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB

**Not proved in this repository.**  `deepmind_halts_iff` is an axiom: it states on this repository's definitions
what `BusyBeaver.M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB.isHalt_iff_acceleration` proves in google-deepmind/cryptids
(`BusyBeaver/BB6/M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB.lean`, commit 3647718, Lean v4.35.0-rc4 with Mathlib), namely
`IsHalt target ↔ CollatzHalts next start` for `target = (load_rle_machine% "1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB").toBB` from the blank tape:
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

namespace H48788

namespace DM

inductive State where
  | S0z (a c : Nat)
  | S0p (a b c : Nat)
  | T1 (j m : Nat)
  | T0 (j m : Nat)
  | T11 (j m : Nat)
  | T3 (j m : Nat)
  | T10 (j m : Nat)
  | Tn (j : Nat)
  | Ea (n : Nat)
  | Eb (k t : Nat)
  | Ec (n : Nat)
  | Ed (k t : Nat)
  deriving DecidableEq, Repr

def start : State := .T1 0 1

def next : State → Option State
  | .S0z a 0 => some (.T1 0 (2 * a + 3))
  | .S0z a (c + 1) => some (.S0p 0 (2 * a + 4) c)
  | .S0p a 0 c => some (.S0p 0 (2 * a + 1) (c + 4))
  | .S0p a 1 c => some (.S0p (a + 2) 0 (c + 2))
  | .S0p a 2 c => some (.S0z (a + 2) c)
  | .S0p a (b + 3) c => some (.S0p (a + 2) b c)
  | .T1 _ 0 => some (.Tn 0)
  | .T1 j 1 => some (.T11 0 (2 * j + 7))
  | .T1 j 2 => some (.S0p 0 (2 * j + 5) 3)
  | .T1 j (m + 3) => some (.T1 (j + 2) m)
  | .T0 j 0 => some (.S0z (j + 1) 0)
  | .T0 _ 1 => none
  | .T0 j 2 => some (.S0z (j + 2) 0)
  | .T0 j (m + 3) => some (.T0 (j + 2) m)
  | .T11 j 0 => some (.T1 0 (2 * j + 6))
  | .T11 j 1 => some (.T3 0 (2 * j + 7))
  | .T11 j 2 => some (.Ea j)
  | .T11 j (m + 3) => some (.T11 (j + 2) m)
  | .T3 j 0 => some (.T1 0 (2 * j + 8))
  | .T3 j 1 => some (.T10 0 (2 * j + 7))
  | .T3 j 2 => some (.Ec j)
  | .T3 j (m + 3) => some (.T3 (j + 2) m)
  | .T10 j 0 => some (.T0 0 (2 * j + 6))
  | .T10 _ 1 => none
  | .T10 _ 2 => none
  | .T10 j (m + 3) => some (.T10 (j + 2) m)
  | .Tn j => some (.Tn (j + 2))
  | .Ea n => some (.Eb 0 (2 * n + 1))
  | .Eb k t => some (.Eb (k + 1) t)
  | .Ec n => some (.Ed 0 (2 * n + 1))
  | .Ed k t => some (.Ed (k + 1) t)

/-- `n` steps of `next` from `start`: DeepMind's `(Option.bind · next)^[n] (some start)` in `CollatzHalts`. -/
def orbit : Nat → Option State
  | 0 => some start
  | n + 1 => Option.bind (orbit n) next

end DM

/-- **Cited, not proved here**: `BusyBeaver.M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB.isHalt_iff_acceleration` (google-deepmind/cryptids, commit 3647718).  The machine halts
from blank tape if and only if the orbit of DeepMind's `next` stops. -/
axiom deepmind_halts_iff : HaltsFromBlank ↔ ∃ n, (DM.orbit n).isNone = true

end H48788
