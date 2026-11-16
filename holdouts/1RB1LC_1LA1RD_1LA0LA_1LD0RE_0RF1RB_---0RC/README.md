# 1RB1LC_1LA1RD_1LA0LA_1LD0RE_0RF1RB_---0RC

bbchallenge id 148028. One of the six-state holdouts whose halting from blank tape is open. Family: **Fibonacci counter feeding a word**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LC |
| B | 1LA | 1RD |
| C | 1LA | 0LA |
| D | 1LD | 0RE |
| E | 0RF | 1RB |
| F | --- | 0RC |

## What it does

Each time the head, in state C, is at the left end reading `0 1 0`, the tape from the head on is
`C>0 (1 0)^z W`, where W is a word of odd blocks of 1s separated by single 0s. Read in pairs of cells the whole tape
is a string of binary digits (the second cell of each pair) and `(1 0)^z` is a run of z zero digits.

From one such moment to the next z grows by one, and the step counts grow by a factor tending to the golden ratio
(1.534, 1.583, 1.604, 1.609 at z = 37, 39, 41, 42): a counter of the Fibonacci kind, whose overflows rewrite W near the
counter. Eleven times in 10^11 steps z falls back to 1 and W is rebuilt longer (a restructure): at steps 105, 184,
529, 660, 3,423, 13,944, 149,177, 370,694, 1,993,257, 442,705,820 and 75,515,153,373 (W grows from 5 to 178 digits).
A halt needs F to read a 0 on blank tape at the right end, so it could only come out of a restructure.

**The word changes by a carry that depends on z.** Run one event again with only z changed
(`py/overflows.py slots`): the next event has W changed in a few digits that sit at fixed places for each z, the
places moving right as z grows, and the number of steps to it grows by the golden ratio (1,760, 2,648, 4,374, 7,384,
..., 2,381,024, 3,852,470 for z = 5..21 from the event at step 2,554,963; ratio 1.6180 at the end). This is the same
mechanism as in the binary sibling `1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB`, with Fibonacci counting in place of
binary: a counter of z digits on the left and a number held in fixed slots of W are advanced by the same ticks, and an
overflow of the left counter adds to W what it counted (a Fibonacci-sized amount, whose normalisation flips several
slot digits at once). Unlike the binary sibling, the change of one overflow is rarely a single carry (26 of the 132
regular pairs of events to 3·10^9 steps; the rest flip digits in both directions, as Zeckendorf normalisation does),
and the numeration of the slots has not been pinned down.

## What is established

**Proved in Lean, kernel only** (`lean/Blank.lean`): the halting configurations (`step_none_iff`); no halt in 10,000
steps (`blank_runs_kernel`).

**Proved in Lean, kernel only** (`lean/Edge.lean`, `lean/EdgeCert.lean`): a closed tape language from windows of four
cells covers the run from blank tape; every halt happens in state F with blank tape from the head on, so the machine
halts exactly when F reaches the blank region at the right (`halt_at_edge`, `halts_iff_edge`).

**Proved in Lean with `native_decide`**: no halt in 10^7 steps (`blank_runs_native`).

**Computed** (trusted C): no halt in 10^11 steps (`tools/c/tmrun.c`; 423 cells, 339 ones). All 179 overflow moments
of the run (C at the left end on `0 1 0`) have the shape `(1 0)^z W` with W of odd blocks.

**Computed** (Python, `py/overflows.py`): the per-overflow changes of W in the run to 3·10^9 steps (26 single
carries, 106 other local changes, 28 restructure pairs); the re-runs of one event with z = 0..21 (fixed change places
for each z, step counts growing by 1.618).

**Heuristic**: the counter is of the Fibonacci kind (ratio of successive overflow gaps tends to 1.618: between
1.6179 and 1.6181 at every overflow from z = 23 on in the epoch from step 442,705,820); the two counters on one clock.

**Open**: the rule from one epoch to the next, whether a restructure can produce the halting configuration, and the
question.

## Status

Open. Lean proves (kernel) the halting configurations, no halt in 10,000 steps and that a halt can only happen at the
right edge; `native_decide` gives no halt in 10^7 steps. The macro structure is observed, not proved: no counter law
is a theorem yet.

## How far it was run

Direct C simulation to 10^11 steps (the 11th restructure at 75,515,153,373). No accelerated run: the per-overflow
change of W is known only by simulation, which costs as many steps as the overflow itself.

## Open questions

* Find the numeration of the slots of W (positions 2, 19, 22, 25, ... at the event of step 2,554,963) so that one
  overflow is W -> W + F(z) for a Fibonacci-type F; the re-runs with every z give the data for it.
* Decode one tick as shift rules and prove the counter laws in Lean.
* Then the restructure, which decides the epochs.
* Build an accelerated simulator on (z, W) once the per-overflow rule is known, to follow many more epochs.

## Layout

| path | what it is |
|---|---|
| `lean/Machine.lean`, `lean/Blank.lean` | the machine, the halting configurations and bounded runs (generated) |
| `lean/EdgeCert.lean`, `lean/Edge.lean` | the closed tape language (from `bbtools.ctl`, K = 4) and the right-edge theorem |
| `py/overflows.py` | the overflow events as (z, W), the changes of W between them, the re-runs with other z |
| `py/tmsim.py` | a plain simulator started from a given tape, run to the next event |

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LC_1LA1RD_1LA0LA_1LD0RE_0RF1RB_---0RC/lean/check.sh
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB1LC_1LA1RD_1LA0LA_1LD0RE_0RF1RB_---0RC 100000000000 records 100000
./tmrun 1RB1LC_1LA1RD_1LA0LA_1LD0RE_0RF1RB_---0RC 3000000000 at C L 1000 > ev.txt
python3 holdouts/1RB1LC_1LA1RD_1LA0LA_1LD0RE_0RF1RB_---0RC/py/overflows.py check ev.txt
python3 holdouts/1RB1LC_1LA1RD_1LA0LA_1LD0RE_0RF1RB_---0RC/py/overflows.py slots ev.txt 2554963 0 22
```

## Pages

- [`pages/holdouts/1RB1LC_1LA1RD_1LA0LA_1LD0RE_0RF1RB_---0RC/explainer.html`](../../pages/holdouts/1RB1LC_1LA1RD_1LA0LA_1LD0RE_0RF1RB_---0RC/explainer.html)
- [`pages/holdouts/1RB1LC_1LA1RD_1LA0LA_1LD0RE_0RF1RB_---0RC/proof-status.html`](../../pages/holdouts/1RB1LC_1LA1RD_1LA0LA_1LD0RE_0RF1RB_---0RC/proof-status.html)
