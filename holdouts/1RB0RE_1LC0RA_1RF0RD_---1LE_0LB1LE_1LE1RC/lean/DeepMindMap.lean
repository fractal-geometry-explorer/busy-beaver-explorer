import Machine

/-!
# A cited result: DeepMind's halts-iff map for 1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC

**Not proved in this repository.**  `deepmind_halts_iff` is an axiom: it states on this repository's definitions
what `BusyBeaver.M_1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC.isHalt_iff_acceleration` proves in google-deepmind/cryptids
(`BusyBeaver/BB6/M_1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC.lean`, commit 3647718, Lean v4.35.0-rc4 with Mathlib), namely
`IsHalt target ↔ CollatzHalts next start` for `target = (load_rle_machine% "1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC").toBB` from the blank tape:
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

namespace H127123

namespace DM

inductive State
  /-- $A(b, k, c)$, the mirror image of `cfg_F b k c`. -/
  | A (b k c : Nat)
  /-- $Odd(p, k, n, m, c)$, the mirror image of `Odd_cfg p k n m c`. -/
  | Odd (p k n m c : Nat)
  /-- $ETail(k, m, c)$, the mirror image of `ETail_cfg k m c`. -/
  | ETail (k m c : Nat)

def start : State := .A 4 0 3

def next : State → Option State
  | .A b k 0 =>
    Nat.casesOn k
      (Nat.casesOn b (some (.A 4 0 3)) fun b =>
       Nat.casesOn b (some (.A 6 0 3)) fun b =>
       Nat.casesOn b (some (.A 3 0 3)) fun b =>
       Nat.casesOn b (some (.A 6 0 3)) fun b =>
       Nat.casesOn b none fun b =>
       some (.A (b + 1) 0 5))
      fun k => some (.A b k 1)
  | .A b k 1 =>
    Nat.casesOn b (some (.A (2 * k + 6) 0 3)) fun b =>
    Nat.casesOn b (some (.A (2 * k + 8) 0 3)) fun b =>
    Nat.casesOn b
      (Nat.casesOn k (some (.A 5 0 0)) fun k => some (.Odd 2 0 0 k 0)) fun b =>
    Nat.casesOn b (some (.A (2 * k + 8) 0 3)) fun b =>
    Nat.casesOn b none fun b =>
    some (.A (b + 1) 0 (2 * k + 7))
  | .A b k (c + 2) =>
    Nat.casesOn b (some (.A 1 (k + 1) c)) fun b =>
    Nat.casesOn b (some (.A 1 (k + 2) c)) fun b =>
    Nat.casesOn b
      (Nat.casesOn k (some (.A 5 0 (c + 1))) fun k => some (.Odd 2 0 0 k (c + 1))) fun b =>
    some (.A (b + 1) (k + 2) c)
  | .Odd p k (n + 1) m c =>
    Nat.casesOn p (some (.Odd 0 (k + 2) n m c)) fun p =>
    some (.Odd p (k + 2) n m c)
  | .Odd p k 0 m c =>
    Nat.casesOn p (some (.ETail k m c)) fun p =>
    Nat.casesOn p (some (.ETail k m c)) fun p =>
    Nat.casesOn m (some (.A (2 * p + 1) 0 (2 * (k + 3) + c))) fun m =>
    some (.Odd p 0 (k + 3) m c)
  | .ETail k 0 c => some (.A (2 * k + c + 7) 0 3)
  | .ETail k 1 c => some (.A (2 * (k + 4) + 1) 0 c)
  | .ETail k (m + 2) c => some (.Odd (k + 4) 0 0 m c)

/-- `n` steps of `next` from `start`: DeepMind's `(Option.bind · next)^[n] (some start)` in `CollatzHalts`. -/
def orbit : Nat → Option State
  | 0 => some start
  | n + 1 => Option.bind (orbit n) next

end DM

/-- **Cited, not proved here**: `BusyBeaver.M_1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC.isHalt_iff_acceleration` (google-deepmind/cryptids, commit 3647718).  The machine halts
from blank tape if and only if the orbit of DeepMind's `next` stops. -/
axiom deepmind_halts_iff : HaltsFromBlank ↔ ∃ n, (DM.orbit n).isNone = true

end H127123
