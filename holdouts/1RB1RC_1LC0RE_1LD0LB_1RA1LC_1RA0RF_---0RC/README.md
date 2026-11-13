# 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC

bbchallenge id 181043. One of the six-state holdouts whose halting from blank tape is open (group G07).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RC |
| B | 1LC | 0RE |
| C | 1LD | 0LB |
| D | 1RA | 1LC |
| E | 1RA | 0RF |
| F | --- | 0RC |

## What it does

At each visit of the left end in state D the tape is `0^inf D>0 1^n R 0^inf`. Each sweep adds two 1s to the block
`1^n` (the head crosses it, turning it into `(10)^(n/2)` and back), and the region `R` after it is transformed by a
map that does not depend on `n`. `R` has exactly 303 cells from visit 138 on:

* the cells of `R` next to the block change at nearly every visit, deeper ones more and more rarely: a counter with
  irregular digits. The deepest change advances about **18 cells per doubling** of the number of visits (202 cells
  into `R` after 8,192 visits, 258 after 131,072);
* the rest of `R` is a **reservoir** of `10` pairs, then an old region ending in `1 1` next to blank tape;
* when the counter has used up the reservoir there is an **event**: the whole block is converted into a new reservoir
  and a new block starts from 0. Events: visit 137 (`R` becomes 303 cells) and visit 167,887 (`R` becomes 335,809
  cells, at step 8.44e10).

The halting transition is F0, reached only as `B>1 1 0` (B1 -> 0RE, E1 -> 0RF): a halt needs B to arrive at the old
region's `1 1` at the fixed end, i.e. the counter at the far end. At 18 cells per doubling the next event is about
2^18,000 visits away.

## Status

Open.

- **Kernel / native_decide:** `lean/Blank.lean` (halting configurations; 10^4 and 10^7 steps).
- **Computed (trusted):** no halt in 1.1e11 steps (direct C run). `c/resetsim.c` cuts the block to 40 cells at every
  visit; `check` mode compares with the true run: `R` agrees at all of the first 30,000 visits except at the event at
  137. The shortened run predicts the event at visit 167,887; the direct run confirms it (`R` 305 -> 335,809 cells
  between steps 8.44e10 and 8.45e10).
- **Heuristic:** the front speed (18 cells per doubling) and the estimate of the next event.
- **Open:** whether any event ends in a halt. Machines 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---1RE and
  1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA1RF_---1RD (same first four states) and 1RB1RD_1LC0LC_1RD1LB_1RF0RE_0RA1RE_---1RB,
  1RB1RD_1LC1RA_---1LD_1LE0RA_1LF0LE_0RB0LB behave the same way.

```sh
gcc -O2 -o resetsim holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC/c/resetsim.c -I tools/c
./resetsim 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC L D 1 40 2 30000 check
T0=2000 STOPEV=1 ./resetsim 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC L D 1 40 2 1000000000   # the event
FRONT=1 T0=200 ./resetsim 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC L D 1 40 2 165800        # the front
```

## Next steps

Find the counter's rule (the digits are runs of odd length between single 0s): if it is a genuine counter, the
event outcome could be computed from the old region, and the question reduced to the sequence of events.

## Pages

- [`pages/holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC/explainer.html`](../../pages/holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC/explainer.html)
- [`pages/holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC/proof-status.html`](../../pages/holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC/lean/check.sh
```
