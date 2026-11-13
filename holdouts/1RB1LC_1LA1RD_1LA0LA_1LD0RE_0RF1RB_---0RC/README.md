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

## What is established

**Proved in Lean, kernel only** (`lean/Blank.lean`): the halting configurations (`step_none_iff`); no halt in 10,000
steps (`blank_runs_kernel`).

**Proved in Lean, kernel only** (`lean/Edge.lean`, `lean/EdgeCert.lean`): a closed tape language from windows of four
cells covers the run from blank tape; every halt happens in state F with blank tape from the head on, so the machine
halts exactly when F reaches the blank region at the right (`halt_at_edge`, `halts_iff_edge`).

**Proved in Lean with `native_decide`**: no halt in 10^7 steps (`blank_runs_native`).

**Computed** (trusted C): no halt in 10^11 steps (`tools/c/tmrun.c`; 423 cells, 339 ones). All 179 overflow moments
of the run (C at the left end on `0 1 0`) have the shape `(1 0)^z W` with W of odd blocks.

**Heuristic**: the counter is of the Fibonacci kind (ratio of successive overflow times tends to 1.618).

**Open**: the rule from one epoch to the next, whether a restructure can produce the halting configuration, and the
question.

## For later

* Decode the counter (a Zeckendorf-type representation is the first guess) and the change it makes to W per
  overflow; then the restructure, which decides the epochs.
* Build an accelerated simulator on (z, W) once the per-overflow rule is known, to follow many more epochs.

## Layout

| path | what it is |
|---|---|
| `lean/Machine.lean`, `lean/Blank.lean` | the machine, the halting configurations and bounded runs (generated) |
| `lean/EdgeCert.lean`, `lean/Edge.lean` | the closed tape language (from `bbtools.ctl`, K = 4) and the right-edge theorem |

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LC_1LA1RD_1LA0LA_1LD0RE_0RF1RB_---0RC/lean/check.sh
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB1LC_1LA1RD_1LA0LA_1LD0RE_0RF1RB_---0RC 100000000000 records 100000
```

## Pages

- [`pages/holdouts/1RB1LC_1LA1RD_1LA0LA_1LD0RE_0RF1RB_---0RC/explainer.html`](../../pages/holdouts/1RB1LC_1LA1RD_1LA0LA_1LD0RE_0RF1RB_---0RC/explainer.html)
- [`pages/holdouts/1RB1LC_1LA1RD_1LA0LA_1LD0RE_0RF1RB_---0RC/proof-status.html`](../../pages/holdouts/1RB1LC_1LA1RD_1LA0LA_1LD0RE_0RF1RB_---0RC/proof-status.html)
