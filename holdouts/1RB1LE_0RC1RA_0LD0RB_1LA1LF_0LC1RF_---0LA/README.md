# 1RB1LE_0RC1RA_0LD0RB_1LA1LF_0LC1RF_---0LA

bbchallenge id 117456. One of the six-state holdouts whose halting from blank tape is open. Family: **counter with a unary end block, gaps doubling, and restructures**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LE |
| B | 0RC | 1RA |
| C | 0LD | 0RB |
| D | 1LA | 1LF |
| E | 0LC | 1RF |
| F | --- | 0LA |

## What it does

It grows mostly to the right (58 cells left of the start, 476 right after 10^11 steps). Each time the head
reaches a new cell at the right end, in state C, the tape ends in `1^7 0 1^7 0 1^k 0 C>0` for most of an epoch, and k
grows by 2 each time while the gap between these moments doubles (exactly, at the last 11 of them; `1^61` at step
66,520,947,462). So a binary counter hides somewhere in the word on the left, which is made of `1^5 0`, `1^6 0^2`,
`1^7 0` and a few other tokens. At restructures (often in bursts; the last four bursts began at steps 2,963,507, 220,322,024,
466,316,545 and 4,568,654,941, after end blocks of 27, 43, 35 and 53 cells) the end block falls back to a few cells
and the word is rewritten. The machine halts only in state F reading a 0.

## What is established

**Proved in Lean, kernel only** (`lean/Blank.lean`): the halting configurations (`step_none_iff`); no halt in 10,000
steps (`blank_runs_kernel`).

**Proved in Lean with `native_decide`**: no halt in 10^7 steps (`blank_runs_native`).

**Computed** (trusted C): no halt in 10^11 steps (`tools/c/tmrun.c`; 534 cells, 382 ones). The right-end records and
the restructure times above.

**Heuristic**: the hidden binary counter.

**Open**: where the counter is, the restructure rule, and the question.

The closed-tape-language search (`bbtools.ctl`, K = 3 to 5) does not confine the halt to an edge: it allows F reading
a 0 with the tape blank on the left and `0100...` on the right.

## For later

* Locate the counter: record the configurations each time the head passes a fixed token of the word, and find the
  part that changes like a binary number between two growths of the end block.
* Decode a restructure: start a direct simulator from the tape just before step 4,568,654,941 and compare the words
  before and after.
* Try larger CTL windows (K = 6 and up), or the mirrored machine, to confine the halt to an edge.

## Layout

| path | what it is |
|---|---|
| `lean/Machine.lean`, `lean/Blank.lean` | the machine, the halting configurations and bounded runs (generated) |

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LE_0RC1RA_0LD0RB_1LA1LF_0LC1RF_---0LA/lean/check.sh
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB1LE_0RC1RA_0LD0RB_1LA1LF_0LC1RF_---0LA 100000000000 records 100000
```

## Pages

- [`pages/holdouts/1RB1LE_0RC1RA_0LD0RB_1LA1LF_0LC1RF_---0LA/explainer.html`](../../pages/holdouts/1RB1LE_0RC1RA_0LD0RB_1LA1LF_0LC1RF_---0LA/explainer.html)
- [`pages/holdouts/1RB1LE_0RC1RA_0LD0RB_1LA1LF_0LC1RF_---0LA/proof-status.html`](../../pages/holdouts/1RB1LE_0RC1RA_0LD0RB_1LA1LF_0LC1RF_---0LA/proof-status.html)
