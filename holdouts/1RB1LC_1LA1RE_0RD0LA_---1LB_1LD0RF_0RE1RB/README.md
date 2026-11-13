# 1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB

bbchallenge id 56057. One of the six-state holdouts whose halting from blank tape is open. Family: **binary counter moving a marker through a word**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LC |
| B | 1LA | 1RE |
| C | 0RD | 0LA |
| D | --- | 1LB |
| E | 1LD | 0RF |
| F | 0RE | 1RB |

## What it does

Each time the head, in state C, is at the left end reading `0 1 0`, the tape from the head on is
`C>0 (1 0)^z W` with W a word of odd blocks of 1s separated by single 0s (binary digits, read in pairs of cells). From
one such moment to the next z grows by one and the step count doubles (a binary counter), and a marker block `1^11`
moves one block right through the periodic end `(1^5 0)^m` of W. When it reaches the end of the tape, W is rebuilt
longer and z starts again (a restructure): in the first 10^11 steps the last three came at steps 17,682,600 (102
digits), 5,745,422,543 (131) and 49,800,461,566 (163). At step 96,162,430,390 the run is at z = 30 with 192 digits.

The machine halts only in state D reading a 0. From configurations of the same shape with random short words it often
halts within a hundred steps (`D>0 1` at the right end), so non-halting depends on the words the run writes.

## What is established

**Proved in Lean, kernel only** (`lean/Blank.lean`): the halting configurations (`step_none_iff`); no halt in 10,000
steps (`blank_runs_kernel`).

**Proved in Lean with `native_decide`**: no halt in 10^7 steps (`blank_runs_native`).

**Computed** (trusted C): no halt in 10^11 steps (`tools/c/tmrun.c`; 385 cells, 312 ones). All 144 overflow moments
of the run have the shape `(1 0)^z W` with W of odd blocks; z rises by one between them except at 16 restructures.

**Heuristic**: the counter is binary (step counts double), the marker moves one block per overflow; random words of
the same shape halt quickly.

**Open**: the restructure rule, why the run's words are safe, and the question.

The closed-tape-language search (`bbtools.ctl`, K up to 6) does not confine the halt to an edge: it allows `D>0 1` with
blank beyond, one cell from the right end.

## For later

* Decode the per-overflow change of W in general (not only in the periodic tail) and the restructure, with a
  simulator started from constructed tapes; then an accelerated simulation over epochs.
* Prove in Lean the marker step through `(1^5 0)^m` (a shift rule with the counter as a black box is not enough: it
  needs the counter's overflow as a macro rule).

## Layout

| path | what it is |
|---|---|
| `lean/Machine.lean`, `lean/Blank.lean` | the machine, the halting configurations and bounded runs (generated) |

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB/lean/check.sh
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB 100000000000 records 100000
```

## Pages

- [`pages/holdouts/1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB/explainer.html`](../../pages/holdouts/1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB/explainer.html)
- [`pages/holdouts/1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB/proof-status.html`](../../pages/holdouts/1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB/proof-status.html)
