# Coq: a halting proof that waits for a halt, and the engine run from start B

This machine is, mirrored and with its states renamed (A→B, B→C, C→D, D→F, E→A, F→E), the table

    U  = 1RB1RA_1LC0RD_1LD1LB_1LF0LE_0LB0LE_0RA---     started in state B

which is also the table of the holdouts 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF (start A),
1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF (start C) and 1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD0RF (start D).
U is the table T3 of DeepMind's halting proof in busycoq pull request 93 with T3's halting transition turned into a
step (E keeps erasing to the left) and T3's D0 turned into a detour that halts exactly when D reads 0 with a 1 on its
left. The reduction, and the scripts, are explained in the folder of the start-A machine:
[`../../1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF/coq/README.md`](../../1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF/coq/README.md).
`mkU.py` there now has a branch for this machine (`perm_U`, `haltsU_iso` with start B and the mirror).

## What is proved (Coq 8.18.0, busycoq BB6 branch at 33209bc)

`mkU.py PR93.v U_B.v 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA0RF B 25 fast` writes a proof of `halts tm c0` for this
machine on busycoq's own definitions. It compiles in about 33 seconds, and `Print Assumptions halt` lists exactly
one assumption:

    HU.run_ok : HU.is_none (HU.run_pow 25 HU.initB) = true

that is, that the accelerated engine, started in B on blank tape, stops within 2^25 of its steps. Every engine step
is proved to be a valid stretch of the machine's run (`stepFast_spec`, `det_step`), and a stop is proved to be a
halt. So a stop of the engine would complete the proof (with 2^K above the stop step, `vm_compute` of `run_ok`).

## The run (22 November 2026)

The engine was extracted from that proof file (the OCaml is byte for byte the one extracted from the start-A file:
the definitions do not depend on the start) and run from blank tape in state B.

- **Validation (computed).** `validateU B 2000 3000000000` runs U directly next to the engine and requires, after
  every fast step, that the direct run reaches exactly the engine's configuration: 1,050 fast steps agree, through
  3·10^9 machine steps.
- **No stop (computed).** The engine passed fast step 18,726,507 without stopping. The tape it then holds has more than
  2^4486 cells, each visited at least once, so **the machine does not halt in its first 2^4486 > 10^1350 steps**.
  This rests on extracted code and OCaml, not on Coq's kernel.
- **Where it leaves its macro rules (computed).** A halt can only happen in a raw step. `ev3 B 13000000` lists every
  entry into raw mode by state, direction and the 8 nearest cells on each side. Through fast step 9.6 million it
  found 15 kinds; the run was stopped before it printed the counts.

  | entry into raw mode | kinds (8 cells each side) | first seen at fast step | what follows |
  |---|---|---|---|
  | D moving left on blank tape | 1 | 3 | the start; D reads 0 with 0s on its left |
  | B moving right, cells `1101 01..` to its left, reading 1 | 3 | 70,741 | B1, then D reads to its right with the 0 that B wrote behind it: cannot halt |
  | D moving right, a 0 on its left | 8 | 71,977 | the same: D was entered by B1, the cell behind it is 0 |
  | D moving left reading 1 | 1 | 2,307,969 | D1 (`0LE`), not D0: no halt at that step |
  | C moving left reading 0, with `1 1 1` on its left | 2 | 72,004 and 5,285,032 | T3's halt (where PR 93's machine stops): D reads 1, E erases three 1s, then the macro rules resume |

  This is the same picture as for start A: the sibling's halting configuration recurs and is survived, and no exit
  met the cells `0, 1` that a halt needs. Observed, not proved. Every raw step is still checked for the halt by the
  engine itself, so a halt anywhere in the run would have stopped it.

For comparison: T4 from B, whose table differs from U only in E1 and D0, halted after 261,156 fast steps on a tape
of 2^2410 cells (`1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD---`), and U from A has run past 2^4439 cells.

## The fast-engine run (22 November 2026)

The same engine extracted with Coq's numbers realized by Zarith (`ExtT4CZ.v`, `buildz.sh` and `runz.ml` in the start-A
folder, explained there) has the old engine's full compressed state at fast step 35,227,304, the old run's last checkpoint
(equal MD5 digests), and is far faster. `runz B ...` ran **627,839,771 fast steps from blank tape without stopping**; the tape
then has more than 2^25751 cells, so **the machine does not halt in its first 10^7751 steps** (extracted code and OCaml,
not Coq's kernel). Every entry into raw mode was in the classes of the table above.

## Files

- `build.sh PR93.v OUTDIR` (with `BUSYCOQ` set): calls the start-A folder's `build.sh` with `START=B` and this
  machine; it compiles the proof skeleton and builds `run`, `ev2`, `ev3`, `pk2` and `validateU`.
- Usage, with `ulimit -s unlimited`: `run B N CHECKPOINT` (saves and resumes an OCaml Marshal checkpoint every 10
  minutes), `validateU B N M`, `ev3 B N`.
