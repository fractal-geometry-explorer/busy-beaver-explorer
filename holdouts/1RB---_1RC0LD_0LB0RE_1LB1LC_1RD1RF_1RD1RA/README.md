# 1RB---_1RC0LD_0LB0RE_1LB1LC_1RD1RF_1RD1RA

bbchallenge id 68492. One of the six-state holdouts whose halting from blank tape is open. Its tape of 10s and 110s holds three counters moved by a linear loop, in phases growing about 3.9-fold.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | --- |
| B | 1RC | 0LD |
| C | 0LB | 0RE |
| D | 1LB | 1LC |
| E | 1RD | 1RF |
| F | 1RD | 1RA |

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`. C (`tools/c/tmrun.c`): no halt in 1,000,000,000 steps.

## What it does

- **Main loop.** With a = `10`, b = `110`: at left-end events `B>0 0 a^x 0 a b^y a^z 0 a b^c 1` goes to
  (x+6, y+1, z-2, c); 451 of 453 consecutive pairs in 10^9 steps (the others are phase changes). Steps per cycle grow
  by 180 per cycle.
- **Phases.** Loops start at (10,1,80,18) step 256,267; (10,1,319,71) step 8,230,627; (10,1,1232,274) step
  501,539,030. Between loops a less regular transition phase (with long 1-blocks) builds the next loop, ~3.9x larger.
- **Halting.** A1 only; A <- F1 <- E1 <- C1, all moving right, so a halt needs C on four 1s in a row. Words 10/110 never
  have three 1s in a row; in 10^9 steps C reads a 1 166,617,942 times
  and the 1s to its right number at most 2.

## Later

- Prove the main loop for all x, y, z, c (the head crosses `a^x` in a zigzag that `bbtools.symtm` does not yet
  cross with words of up to 3 cells; a 6-cell word or a hand-made shift rule may be needed).
- Describe the transition phase as a function of (x, y, c) at the end of a loop; if the next loop's start is a
  closed form, the run is a recursive map like 1RB1RF_1LC1LF's.

## First look

Growth class **fixed/power** (left: power, exponent 0.274; right: fixed,
exponent 0.26). After 1,000,000,000 steps: 6,110 cells visited (4,198 left of the
start, 261 right), 3,396 ones.

- left, step 981,963,529: `C>0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `
- left, step 999,322,348: `C>0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `

## Pages

- [`pages/holdouts/1RB---_1RC0LD_0LB0RE_1LB1LC_1RD1RF_1RD1RA/explainer.html`](../../pages/holdouts/1RB---_1RC0LD_0LB0RE_1LB1LC_1RD1RF_1RD1RA/explainer.html)
- [`pages/holdouts/1RB---_1RC0LD_0LB0RE_1LB1LC_1RD1RF_1RD1RA/proof-status.html`](../../pages/holdouts/1RB---_1RC0LD_0LB0RE_1LB1LC_1RD1RF_1RD1RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB---_1RC0LD_0LB0RE_1LB1LC_1RD1RF_1RD1RA/lean/check.sh
```

## Accelerated run

Trusted computation: `python3 tools/py/bbtools/rleaccel.py 1RB---_1RC0LD_0LB0RE_1LB1LC_1RD1RF_1RD1RA 6 154800000` runs 154,800,000 macro steps from blank tape without a halt, more than 4.41·10^11
machine steps (tape: 52,530 cells). The simulator codes the tape in runs, crosses a run in one step and jumps cycles whose
one-cycle rule it has first proved symbolically; it is tested cell for cell against direct runs
(`tools/tests/test_rleaccel.py`).
