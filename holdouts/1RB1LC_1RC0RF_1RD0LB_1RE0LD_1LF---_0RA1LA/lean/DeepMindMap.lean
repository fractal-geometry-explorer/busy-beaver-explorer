import Machine

/-!
# A cited result: DeepMind's halts-iff map for 1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA

**Not proved in this repository.**  `deepmind_halts_iff` is an axiom: it states on this repository's definitions
what `BusyBeaver.M_1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LFHHH_0RA1LA.isHalt_iff_acceleration` proves in google-deepmind/cryptids
(`BusyBeaver/BB6/M_1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LFHHH_0RA1LA.lean`, commit 3647718, Lean v4.35.0-rc4 with Mathlib), namely
`IsHalt target ↔ CollatzHalts next start` for `target = (load_rle_machine% "1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA").toBB` from the blank tape:
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

namespace H66813

namespace DM

private abbrev p0 : List (Fin 2) := [0]

private abbrev p001010 : List (Fin 2) := [0, 0, 1, 0, 1, 0]

private abbrev p0010 : List (Fin 2) := [0, 0, 1, 0]

private abbrev p0010110 : List (Fin 2) := [0, 0, 1, 0, 1, 1, 0]

private abbrev p00 : List (Fin 2) := [0, 0]

private abbrev p010 : List (Fin 2) := [0, 1, 0]

private abbrev pnil : List (Fin 2) := []

inductive State where
  /-- $R_1(n) := 0^\infty\,(1100)^n\,100\,\mathrm{A}{>}\,0^\infty$. -/
  | R1 (n : Nat)
  /-- $R_2(n) := 0^\infty\,(1100)^n\,100100\,\mathrm{A}{>}\,0^\infty$. -/
  | R2 (n : Nat)
  /-- $Q(n) := 0^\infty\,(1100)^n\,111100\,\mathrm{A}{>}\,0^\infty$. -/
  | Q (n : Nat)
  /-- $S_4(n) := 0^\infty\,(1100)^n\,111100100100\,\mathrm{A}{>}\,0^\infty$. -/
  | S4 (n : Nat)
  /-- $S_6(n) := 0^\infty\,(1100)^n\,11111100100100\,\mathrm{A}{>}\,0^\infty$. -/
  | S6 (n : Nat)

def start : State := .S6 1

def next_P (n : Nat) : Option State :=
  Nat.casesOn n (some (.S6 1)) fun n =>
  Nat.casesOn n (some (.S4 0)) fun n' =>
  some (.S6 n')

def next_R1 (n : Nat) : Option State :=
  Nat.casesOn n (some (.R1 4)) fun n =>
  Nat.casesOn n (some (.R1 6)) fun n' =>
  some (.R1 (n' + 7))

def next_T1 (n : Nat) : Option State :=
  Nat.casesOn n (some (.R1 7)) fun n' =>
  some (.R1 (n' + 8))

def next_R3 (n : Nat) : Option State :=
  Nat.casesOn n (next_T1 4) fun n =>
  Nat.casesOn n (next_T1 6) fun n' =>
  next_T1 (n' + 7)

def next_HubTail_r_R2 : Nat → Nat → Option State
  | a, 0 => some (.R1 (a + 8))
  | a, 1 => some (.R2 (a + 11))
  | a, 2 => some (.Q (a + 19))
  | a, 3 => some (.R2 (a + 26))
  | a, 4 => next_R3 (a + 32)
  | a, w' + 5 => next_HubTail_r_R2 (a + 31) w'

def next_HubTail_r_3 : Nat → Nat → Option State
  | a, 0 => some (.R1 (a + 10))
  | a, 1 => some (.Q (a + 16))
  | a, 2 => some (.R2 (a + 23))
  | _, 3 => none
  | a, 4 => some (.R2 (a + 37))
  | a, w' + 5 => next_HubTail_r_3 (a + 31) w'

def next_HubTail_r_4 : Nat → Nat → Option State
  | a, 0 => next_T1 (a + 9)
  | a, 1 => some (.R2 (a + 15))
  | a, 2 => some (.R1 (a + 25))
  | a, 3 => some (.S6 (a + 28))
  | a, 4 => some (.R2 (a + 41))
  | a, w' + 5 => next_HubTail_r_4 (a + 31) w'

def next_HubTail_r_5 : Nat → Nat → Option State
  | a, 0 => some (.R1 (a + 12))
  | a, 1 => some (.R1 (a + 15))
  | a, 2 => some (.R2 (a + 26))
  | a, 3 => some (.Q (a + 34))
  | a, 4 => next_T1 (a + 38)
  | a, w' + 5 => next_HubTail_r_5 (a + 31) w'

structure NextScanBundle where
  p0 : Nat → Option State
  p001010 : Nat → Option State
  p0010 : Nat → Option State
  p0010110 : Nat → Option State
  p00 : Nat → Option State
  p010 : Nat → Option State
  pnil : Nat → Option State
  p0_next : Nat → Option State
  p0010_next : Nat → Option State

def next_HubW8 (nb : NextScanBundle) : Nat → Nat → Option State
  | a, 0 => nb.p0 (a + 4)
  | a, 1 => nb.p010 (a + 7)
  | a, 2 => nb.p00 (a + 16)
  | a, 3 => nb.p0010 (a + 22)
  | a, 4 => nb.p001010 (a + 28)
  | a, w' + 5 => next_HubW8 nb (a + 31) w'

def next_ScanBundle_r_Q (b : Nat) : NextScanBundle :=
  Nat.rec
    { p0 := fun a => some (.R1 (a + 4))
      p001010 := fun a => next_P (a + 8)
      p0010 := fun a => some (.R2 (a + 4))
      p0010110 := fun a => next_P (a + 10)
      p00 := fun a => some (.R1 (a + 4))
      p010 := fun a => next_P (a + 7)
      pnil := fun a => next_P (a + 5)
      p0_next := fun a => some (.S6 (a + 2))
      p0010_next := fun a => some (.R1 (a + 9)) }
    (fun _ nb =>
      { p0 := nb.p0_next
        p001010 := fun a => nb.p0 (a + 6)
        p0010 := nb.p0010_next
        p0010110 := fun a => nb.p00 (a + 9)
        p00 := fun a => nb.p010 (a + 3)
        p010 := fun a => nb.pnil (a + 4)
        pnil := fun a => nb.p0 (a + 3)
        p0_next := fun a => next_HubW8 nb 0 ((a + 3) / 2)
        p0010_next := fun a => nb.p0010110 (a + 5) })
    b

def next_ScanBundle_r_S6 (b : Nat) : NextScanBundle :=
  Nat.rec
    { p0 := fun a => some (.S4 (a + 9))
      p001010 := fun a => next_T1 (a + 11)
      p0010 := fun a => some (.R1 (a + 10))
      p0010110 := fun _ => none
      p00 := fun a => some (.R2 (a + 11))
      p010 := fun a => some (.R1 (a + 14))
      pnil := fun a => next_T1 (a + 8)
      p0_next := fun a => next_HubTail_r_4 0 ((a + 1) / 2 + 1)
      p0010_next := fun a => next_HubTail_r_3 0 ((a + 8) / 2) }
    (fun _ nb =>
      { p0 := nb.p0_next
        p001010 := fun a => nb.p0 (a + 6)
        p0010 := nb.p0010_next
        p0010110 := fun a => nb.p00 (a + 9)
        p00 := fun a => nb.p010 (a + 3)
        p010 := fun a => nb.pnil (a + 4)
        pnil := fun a => nb.p0 (a + 3)
        p0_next := fun a => next_HubW8 nb 0 ((a + 3) / 2)
        p0010_next := fun a => nb.p0010110 (a + 5) })
    b

def next_ScanBundle_r_S4 (b : Nat) : NextScanBundle :=
  Nat.rec
    { p0 := fun a => some (.R2 (a + 7))
      p001010 := fun a => some (.R1 (a + 9))
      p0010 := fun a => some (.R1 (a + 9))
      p0010110 := fun a => some (.S4 (a + 9))
      p00 := fun a => next_T1 (a + 4)
      p010 := fun a => some (.Q (a + 9))
      pnil := fun a => some (.R1 (a + 6))
      p0_next := fun a => next_HubTail_r_5 0 ((a + 1) / 2 + 1)
      p0010_next := fun a => some (.R1 (a + 13)) }
    (fun _ nb =>
      { p0 := nb.p0_next
        p001010 := fun a => nb.p0 (a + 6)
        p0010 := nb.p0010_next
        p0010110 := fun a => nb.p00 (a + 9)
        p00 := fun a => nb.p010 (a + 3)
        p010 := fun a => nb.pnil (a + 4)
        pnil := fun a => nb.p0 (a + 3)
        p0_next := fun a => next_HubW8 nb 0 ((a + 3) / 2)
        p0010_next := fun a => nb.p0010110 (a + 5) })
    b

def next_R2 (n : Nat) : Option State :=
  Nat.casesOn n (some (.R1 4)) fun n' =>
  next_HubTail_r_R2 0 (n' / 2)

def next_Q (n : Nat) : Option State :=
  Nat.casesOn n (some (.R1 6)) fun n' =>
  (next_ScanBundle_r_Q n').p0010110 2

def next_S4 (n : Nat) : Option State :=
  Nat.casesOn n (some (.R1 10)) fun n' =>
  (next_ScanBundle_r_S4 n').p0010110 2

def next_S6 (n : Nat) : Option State :=
  Nat.casesOn n (some (.R1 9)) fun n =>
  Nat.casesOn n (next_HubTail_r_3 0 2) fun n' =>
  (next_ScanBundle_r_S6 n').p0010110 2

def next : State → Option State
  | .R1 n => next_R1 n
  | .R2 n => next_R2 n
  | .Q n => next_Q n
  | .S4 n => next_S4 n
  | .S6 n => next_S6 n

/-- `n` steps of `next` from `start`: DeepMind's `(Option.bind · next)^[n] (some start)` in `CollatzHalts`. -/
def orbit : Nat → Option State
  | 0 => some start
  | n + 1 => Option.bind (orbit n) next

end DM

/-- **Cited, not proved here**: `BusyBeaver.M_1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LFHHH_0RA1LA.isHalt_iff_acceleration` (google-deepmind/cryptids, commit 3647718).  The machine halts
from blank tape if and only if the orbit of DeepMind's `next` stops. -/
axiom deepmind_halts_iff : HaltsFromBlank ↔ ∃ n, (DM.orbit n).isNone = true

end H66813
