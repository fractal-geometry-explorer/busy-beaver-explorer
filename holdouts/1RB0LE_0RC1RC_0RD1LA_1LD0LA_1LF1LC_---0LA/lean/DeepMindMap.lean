import Machine

/-!
# A cited result: DeepMind's halts-iff map for 1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA

**Not proved in this repository.**  `deepmind_halts_iff` is an axiom: it states on this repository's definitions
what `BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.isHalt_iff_acceleration` proves in google-deepmind/cryptids
(`BusyBeaver/BB6/M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.lean`, commit 3647718, Lean v4.35.0-rc4 with Mathlib), namely
`IsHalt target ↔ CollatzHalts next start` for `target = (load_rle_machine% "1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA").toBB` from the blank tape:
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

namespace H133227

namespace DM

inductive State
  | D0 (a b d : Nat)
  | D1 (a b d : Nat)
  | H (a b m : Nat)
  | B (a k b d : Nat)
  | A_pos (a k q m : Nat)
  | A_zero (a q m : Nat)

def start : State := .D0 0 0 4

def next : State → Option State
  | .D1 0 0 d => some (.D1 0 0 (d + 1))
  | .D1 0 (b + 1) d => some (.D1 1 b (d + 2))
  | .D1 (a + 1) b d => some (.B a 0 b d)
  | .D0 a b 0 =>
    Nat.casesOn a
      (Nat.casesOn b (some (.D1 0 0 1)) fun b => some (.D1 1 b 2))
      fun a => some (.B a 0 b 0)
  | .D0 a b 1 =>
    Nat.casesOn b
      (Nat.casesOn a (some (.D0 0 0 4)) fun a => some (.B (a + 1) 0 0 0))
      fun b => some (.D1 (a + 2) b 3)
  | .D0 a b 2 =>
    Nat.casesOn a (some (.D1 1 b 2)) fun a => some (.B a 0 (b + 1) 0)
  | .D0 a b (d + 3) => some (.D0 (a + 2) b (d + 1))
  | .H a b 0 =>
    Nat.casesOn a none fun a =>
    some (.D1 (if a = 0 then 1 else a + 1) (b + 1) 5)
  | .H a b 1 => some (.D1 (a + 2) (b + 1) 2)
  | .H a b (m + 2) =>
    Nat.casesOn a none fun a =>
    Nat.casesOn a
      (Nat.casesOn m (some (.D1 2 (b + 2) 3)) fun m =>
       Nat.casesOn m (some (.D1 1 (b + 3) 2)) fun m =>
       some (.D0 2 (b + 3) (m + 1)))
      fun a => some (.H a (b + 2) m)
  | .B a k (b + 1) d => some (.B a (k + 1) b (d + 2))
  | .B a 0 0 d =>
    Nat.casesOn a (some (.D0 0 0 (d + 4))) fun a =>
    Nat.casesOn a none fun a =>
    Nat.casesOn a
      (Nat.casesOn d (some (.D1 1 2 2)) fun d => some (.D0 2 2 (d + 1)))
      fun a => some (.H a 1 (d + 1))
  | .B a (k + 1) 0 d => some (.A_pos a k 0 (d + 3))
  | .A_zero a q m => some (.D1 (a + 2) q m)
  | .A_pos a 0 q m =>
    Nat.casesOn a none fun a =>
    Nat.casesOn q
      (some (.D1 (if a = 0 then 1 else a + 1) 0 (m + 2)))
      fun q => some (.D1 (if a = 0 then 1 else a + 1) (q + 1) (m + 2))
  | .A_pos a 1 q m =>
    Nat.casesOn a (some (.D1 1 q m)) fun a =>
    some (.A_pos a q 0 (m + 2 * q + 3))
  | .A_pos a 2 q m => some (.A_zero a q m)
  | .A_pos a (k + 3) q m => some (.A_pos a k (q + 1) m)

/-- `n` steps of `next` from `start`: DeepMind's `(Option.bind · next)^[n] (some start)` in `CollatzHalts`. -/
def orbit : Nat → Option State
  | 0 => some start
  | n + 1 => Option.bind (orbit n) next

end DM

/-- **Cited, not proved here**: `BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.isHalt_iff_acceleration` (google-deepmind/cryptids, commit 3647718).  The machine halts
from blank tape if and only if the orbit of DeepMind's `next` stops. -/
axiom deepmind_halts_iff : HaltsFromBlank ↔ ∃ n, (DM.orbit n).isNone = true

end H133227
