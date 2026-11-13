# 1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD

bbchallenge id 5788. One of the six-state holdouts whose halting from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LD |
| B | 1RC | 0RF |
| C | 1LA | 1RF |
| D | 0LA | 0RE |
| E | 1LD | --- |
| F | 0RA | 0RD |

**Family:** Nested ternary counter (segments drained at rates 2*3^j, mirrored pair).

A nested ternary counter like a draining odometer: segments of 111-blocks near the growing end lose 2*3^j blocks per cycle while new segments are made at the far end; it survives the collapses seen so far and does not halt in 10^19 steps (accelerated simulation).

## Equivalence

`1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD` (c2, id 5788) and `1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB` (c1, id 49413) are mirror images: swap left and right in c1 and relabel A->E, B->D,
C->A, D->B, E->C, and you get c2's table. So c1 from blank is c2 mirrored and started in state E. They follow the
same law with different numbers; the scripts are in `holdouts/1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD/py/` and `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/c/`.

## What it does

At each step where the head writes a new cell at the growing end (the right end for c2, the left end for c1), the
tape read from the far end, as lengths of runs of 1s (single 0s left out), is

    6 3^x1 9 3^x2 9 ... 9 3^xm  TAIL

blocks `111` separated by single 0s, cut into segments by markers `1^9`. The head sweeps the whole tape (11 shift
rules in `lean/Rules.lean`). These moments come in cycles of three.

## The map (partial)

Between collapses, per cycle the segment j places from the growing end loses 2*3^j blocks (6, 18, 54, 162, ...),
like an odometer turned backwards, with occasional off-by-one irregularities next to the junk at the ends; new,
large segments of the form a*3^k - 2 are made at the far end. When a segment near the growing end runs out the last
segments merge (a collapse) and the drain starts again with fewer segments. The rule at the far end and at
collapses is not pinned down, so this is not yet a complete map. Segments next to the growing end of c2 in the macro
run (from the growing end):

| step | last four segments |
|---|---|
| 2.30e15 | 47 143 3833 5717 |
| 2.72e16 | 22 65 3599 5015 |
| 2.90e17 | 3 7 3425 4493 |
| 3.00e17 | 3399 4405 23281 180681 (after a collapse) |
| 9.06e18 | 3353 4271 22879 179475 |

c1 had its collapse near 2e12 steps and at 3.6e18 has `371 43406 155472 33394`.

## Halting condition

Not known. Halting needs the head in state D on a 1 with a 1 to its right (D1 -> 0RE, E1 halts); inside the draining regime this does not occur, and what a collapse does in general is not known.

## How far

The macro simulator `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/c/msim.c` (4-cell blocks, two-block window, whole runs crossed in steady state,
exact 128-bit step counts, checked against `tools/c/tmrun.c` by `py/check_msim.py`) runs both machines to 1e19 steps
without a halt: `data/c2_msim.txt` ends at 10,000,000,000,378,843,465 and `data/c1_msim.txt` at
10,000,000,002,400,213,340.

At the end, c2's next collapse is the 4,261-block segment (18 per cycle), about 240 cycles away; c1's is the
370-block one (6 per cycle), about 62 cycles away. Cycles have been getting longer by a factor of about 2 on
average, so these lie near 1e38 steps (c1) and far beyond (c2): heuristic estimates only.

## Reproduce

```sh
gcc -O2 -o msim holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/c/msim.c
./msim 1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD 4 1e19 - 1          # c2, snapshot at each fresh block on the right
./msim 1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB 4 1e19 - 1 l        # c1, on the left
python3 holdouts/1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD/py/cmap.py c2 4.5e9   # the draining law on the direct run
python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/check_msim.py 2e9
```

## Further work

The far-end generator and the collapse rule, which would make the map complete and let it be iterated past the next
collapses; then a Lean proof of one cycle of the drain from the shift rules.

## What is proved, and how firmly

| level | claim | where |
|---|---|---|
| kernel | **The halting configurations.** The machine stops exactly when it reads the symbol of a halting transition (E1); the generated statement covers every configuration. | `step_none_iff`, `lean/Blank.lean` |
| kernel | **No halt in the first 10,000 steps.** The list simulator of the shared library, proved to agree with the machine's semantics, runs 10,000 steps from blank tape without a halt, evaluated by Lean's kernel. | `blank_runs_kernel`, `lean/Blank.lean` |
| native | **No halt in the first 10^7 steps.** The same run, evaluated by compiled code. | `blank_runs_native`, `lean/Blank.lean` |
| trusted | **No halt in the first 10^9 steps.** The C simulator `tools/c/triage.c` runs 10^9 steps without a halt; at the end 99,142 cells have been visited and 42,433 of them hold a 1. | `holdouts/triage.json` |
| heuristic | **Growth shape: exp/sqrt.** Left of the start, the visited part of the tape grows like the square root of the step count, the signature of a head sweeping back and forth across the whole tape and adding a cell or a few at the end of each sweep (a bouncer-like shape) (fitted exponent 0.489). Right of the start it grows like the logarithm of the step count: each new cell costs a roughly constant factor more time, the signature of a counter or of a Collatz-like map whose values are written on the tape (fitted exponent 0.062). | `tools/py/bbtools/triage.py` |
| kernel | **11 shift rules.** For every n, the head crosses n copies of a short word in a fixed number of steps per copy and leaves another word behind (for example the head going left over `0111` and leaving `0100`, 18 steps a copy; these cross the 111-blocks of the counter). Generated and proved by `bbtools.symtm`, checked by Lean's kernel. | `lean/Rules.lean`, generated by `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/rules.py` |
| trusted | **No halt in the first 10^19 steps.** A macro simulator (blocks of 4 cells, crossing long runs of equal blocks in one go; it agrees with the direct simulator at 2x10^9 steps) runs 10,000,000,000,378,843,465 steps without a halt, through the collapses at about 3x10^17. | `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/c/msim.c`; output in `holdouts/1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD/data/c2_msim.txt` |
| heuristic | **The draining law.** Between collapses, the segment j places from the growing end loses 2*3^j blocks per cycle (6, 18, 54, 162, ... per sampled cycle of the macro run), with occasional off-by-one irregularities at the junk near the ends. It is checked on the cycles of the direct run to 4.5x10^9 steps (failing exactly at the collapses) and on the macro run to 10^19; the far-end rule that makes new segments is not pinned down. | `python3 holdouts/1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD/py/cmap.py c2` |
| heuristic | **The next collapse.** At 10^19 steps the three segments next to the growing end hold 22,849, 4,261 and 3,351 blocks; the 4,261 runs out first, after about 240 more cycles; cycles have been getting longer by a factor of about 2 on average, so that is far beyond reach. | `holdouts/1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD/data/c2_msim.txt` |
| open | **Does it halt from blank tape?** Not known. Halting needs the head in state D on a 1 with a 1 to its right (D1 -> 0RE, E1 halts); inside the draining regime this does not occur, and what a collapse does in general is not known. |  |

## Lean

`lean/Rules.lean` is generated by `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/rules.py` (one script for all eight machines of this worker;
`--check` compares the files instead of writing them) and is listed in `lean/check.sh` after `Blank.lean`:

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD/lean/check.sh
python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/rules.py --check
```

## Pages

- [`pages/holdouts/1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD/explainer.html`](../../pages/holdouts/1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD/explainer.html)
- [`pages/holdouts/1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD/proof-status.html`](../../pages/holdouts/1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD/proof-status.html)
