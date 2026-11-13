# 1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC

bbchallenge id 132695. One of the six-state holdouts whose halting from blank tape is open. (group G07).
Family: **counter that overflows at the left end**. Decision: **open**. Same table as 74982, mirrored.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RE |
| B | 1LC | 1LA |
| C | 1RA | 0LD |
| D | 1LC | 0LE |
| E | 0LF | 0RA |
| F | --- | 1RC |

## What it does

This machine is the table of [`1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC`](../1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC/README.md) (74982) read in a mirror, with the states renamed: A, B, C,
D, E, F here are C, F, B, A, D, E there (`is_mirror`, Lean). So its run from blank tape is, cell for cell in the
mirror, the run of 74982 started on blank tape in state C, and everything proved there for every tape holds here.
The two machines start in different states, so they are two separate halting questions.

In this machine's own orientation the tape is

```
d 1 xk 1 ... 1 x2 1 x1 1 1 (01)^(n+1)        the head arrives from the right, on the first 1 left of the units
```

- **The units** `01` at the right end (runs of a single 1) are 74982's wall. The head crosses them twice per sweep
  and one unit is added at the blank end each time.
- **The counter** is the digits x1, x2, ..., xk on every second cell, with a 1 between neighbours, and a last cell d
  at the left end of the tape. Read as runs of 1s separated by single 0s this is a row of odd runs: a digit 0 ends a
  run. The rewrites seen in a run (`(1,3) -> 5`, `(3,3) -> 7`, ...) are the carry of 74982's automaton: three carry
  states a, b, c; a: 0 becomes 1 and the carry stops, 1 becomes 0 and it goes on in b; b: 0 becomes 1 (go on in a),
  1 becomes 0 (go on in c); c: 0 stays (c), 1 stays (a).

An **overflow** is a carry that runs through all the digits and reads the last cell d at the left end. What it does
then is proved in Lean for every counter (`lean/Ends.lean` in the folder of 74982):

| carry state at d | d = 0 | d = 1 |
|---|---|---|
| a | d becomes 1 | **extension**: the counter gains a digit |
| b | **the machine halts** | **conversion**: all the units become counter digits |
| c | **conversion** | **the machine halts** |

After every one of these the last cell is 1, so from the first overflow on the machine halts exactly when a carry
reaches the left end **in state c**. On the tape that is the head arriving on the leftmost 1 in state D with a 1
just crossed (`D1 -> 0LE`, `E0 -> 0LF`, `F0` halts): the head comes off the left end in state E instead of D, as
`halts_iff_edge` says.

## The run from blank tape

16 steps from blank tape the machine is at an arrival with one unit, the single digit 1 and last cell 1
(`twin_arrival`, kernel). From there on it is the event system of 74982:

- `twin_halts_iff_events` (Lean, kernel only): **the machine halts from blank tape if and only if the event system
  `evstep` halts from (wall of 1 pair, digits [1], last cell 1).**
- The overflows of the run are events of that system (`py/events.py twin` in the folder of 74982, which also
  compares the system with the machine on the first 200,000 steps):

  | sweep | step of the overflow | event | units before | digits after |
  |---|---|---|---|---|
  | 1 | 28 | conversion | 1 | 3 |
  | 3 | 91 | conversion | 2 | 6 |
  | 8 | 309 | extension | 5 | 7 |
  | 10 | 450 | conversion | 7 | 15 |
  | 21 | 1,252 | extension | 11 | 16 |
  | 53 | 7,545 | conversion | 43 | 60 |
  | 410,976 | 506,587,790,058 | conversion | 410,923 | 410,984 |

  (The overflow at step 3 is before the first arrival.) The steps are those found by `c/tok.c`; the sweeps and
  events are computed by the event system.
- `twin_conversion`, `twin_halts_iff_after` (Lean, with `native_decide` for the 410,975 sweeps): the 410,976th
  sweep is a conversion of 410,923 units, and the machine halts from blank tape if and only if the event system
  halts from the counter it leaves: 410,922 ones, a 0, the 60 marks of the last carry and a 1 (410,984 digits), last
  cell 1, one unit. So the machine does not halt in the first 5·10^11 steps, and the last conversion is why the
  tape changed from mostly units to a wide region of short runs.

## Where it stands

**Open.** The next overflow needs a carry through 410,984 digits. On small counters the number of sweeps to the next
overflow doubles about every 3 digits, which puts it at the order of 2^(1.3·10^5) sweeps. Whether it is an
extension, a conversion or a halt is not known, and no shortcut was found: the sequence of carry states leaving a
prefix of the counter, kept as a straight-line program, stops compressing after about 150 digits (the program grows
from 5,000 nodes at 100 digits to 7.3·10^6 at 200; `py/events.py program` in the folder of 74982).

Observed on other counters (not proved, and no guide to this one): of 300 random counters of 30 to 60 digits
followed to their first halt or conversion, 170 end in a halt.

## Status

- **Kernel:** `step_none_iff`, `blank_runs_kernel` (`lean/Blank.lean`); `halts_iff_edge` (`lean/Edge.lean`).
  In `holdouts/1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC/lean/`: every sweep and every end event for every counter (`Sweep.lean`, `Ends.lean`),
  `is_mirror`, `halts_mirror`, `twin_arrival`, `twin_halts_iff_events` (`Twin132695.lean`). The table of this
  machine is restated in that file, because the two folders' Lean modules cannot be imported together; it is the text
  of this folder's generated `lean/Machine.lean`.
- **native_decide:** `blank_runs_native` (10^7 steps); `twin_conversion`, `twin_halts_iff_after`.
- **Trusted computation:** `c/tok.c`, an exact run-length simulator (it agrees with `tools/c/tmrun.c` on the number
  of 1s at step 10,000,208,949), runs 10^16 steps: 5.8·10^7 visits of the right end, no halt; the head reads a 0 with
  only blank tape to its left only at the eight overflows above, each time in state D. `py/events.py twin`.
- **Open:** the kind of the next overflow.

## Pages

- [`pages/holdouts/1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC/explainer.html`](../../pages/holdouts/1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC/explainer.html)
- [`pages/holdouts/1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC/proof-status.html`](../../pages/holdouts/1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC/lean/check.sh
holdouts/1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC/lean/check.sh                                   # Ends.lean, Twin132695.lean
python3 holdouts/1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC/py/events.py twin
(cd tools/py && python3 -m bbtools.ctl 1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC 4 lean H132695 Blank) | diff - holdouts/1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC/lean/EdgeCert.lean
gcc -O2 -o tok holdouts/1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC/c/tok.c
./tok 1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC 1e16 A R 100000      # the tape every 10^5 visits of the right end, ~3 min
./tok 1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC 1e16 D L 1           # every time D reads a 0 with only blank to its left (the overflows)
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC`](../1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC/README.md): rename A→C, B→F, C→B, D→A, E→D, F→E and exchange left and right; it is this table started in state D, in a mirror

<!-- end of related machines -->
