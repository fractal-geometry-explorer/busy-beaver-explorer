# 1RB0LD_0LC0RE_1LA0RD_0RB0LF_1RC1LA_0RB---

bbchallenge id 55410. One of the six-state holdouts whose halting from blank tape is open. Its run looks chaotic on a tape that grows roughly logarithmically.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LD |
| B | 0LC | 0RE |
| C | 1LA | 0RD |
| D | 0RB | 0LF |
| E | 1RC | 1LA |
| F | 0RB | --- |

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`. C (`tools/c/tmrun.c`): no halt in 10,000,000,000 steps.

## What it does

The tape is a mixture of the words <code>10</code>, <code>1000</code> and <code>110</code> with no visible order, and the head works through it in a zigzag, one cell right and three left (states D and B alternating). The right end is a wall of repeated <code>110</code>s, which the run occasionally extends. Unlike a counter, nothing on the tape doubles or repeats; the visited region grows by only about 20 to 25 cells per tenfold increase in time.

- **Growth.** Cells visited: 163 (10^6), 174 (10^7), 221 (10^8), 238 (10^9), 257 (10^10) steps.
- **Halting.** Only F1 halts; F is entered only from D1 (`0LF`). In 10^8 steps D reads 1 3,571,420 times, always with a 0
  to its left.
- **No structure found.** `bbtools.macro` with blocks of 3 / 6 cells needs one macro step per ~3 / ~6-7 steps
  over 10^7 steps; `bbtools.cycles` (k = 4) finds no linear cycle in 10^7 steps; CTL windows up to 8 cells do not close (group scan).

## Later

- Look for an invariant (a regular language of tapes, or a weighted count) that excludes the halting pattern;
  try CTL with word-based windows (the tape is made of a few words) instead of fixed cell windows.

## First look

Growth class **fixed/fixed** (left: fixed, exponent 0.074; right: fixed,
exponent 0.082). After 1,000,000,000 steps: 239 cells visited (46 left of the
start, 192 right), 103 ones.

## Pages

- [`pages/holdouts/1RB0LD_0LC0RE_1LA0RD_0RB0LF_1RC1LA_0RB---/explainer.html`](../../pages/holdouts/1RB0LD_0LC0RE_1LA0RD_0RB0LF_1RC1LA_0RB---/explainer.html)
- [`pages/holdouts/1RB0LD_0LC0RE_1LA0RD_0RB0LF_1RC1LA_0RB---/proof-status.html`](../../pages/holdouts/1RB0LD_0LC0RE_1LA0RD_0RB0LF_1RC1LA_0RB---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LD_0LC0RE_1LA0RD_0RB0LF_1RC1LA_0RB---/lean/check.sh
```
