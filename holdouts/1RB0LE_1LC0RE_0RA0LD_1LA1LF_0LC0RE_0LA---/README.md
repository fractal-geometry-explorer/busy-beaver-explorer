# 1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LA---

bbchallenge id 2327. One of the six-state holdouts whose halting from blank tape is open. Its run looks chaotic on a tape that grows roughly logarithmically.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 1LC | 0RE |
| C | 0RA | 0LD |
| D | 1LA | 1LF |
| E | 0LC | 0RE |
| F | 0LA | --- |

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`. C (`tools/c/tmrun.c`): no halt in 10,000,000,000 steps.

## What it does

This machine differs from the holdout 1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0RE--- in three transitions (D1, E1, F0) and behaves the same way: a wall of repeated <code>101</code>s at the left end whose length wanders, and an irregular mixture of the words <code>10</code>, <code>1000</code> and <code>110</code> behind it that is rewritten over and over. The visited region grows by about 30 cells per tenfold increase in time (191 cells at 10<sup>9</sup> steps, 221 at 10<sup>10</sup>).

- **Growth.** Cells visited: 191 (10^9), 221 (10^10) steps.
- **Halting.** Only F1 halts; F is entered only from D1 (`1LF`), 15 times in 10^8 steps, always with a 0 to the left.
- **No structure found.** `bbtools.macro` with blocks of 3 / 6 cells needs one macro step per ~3 / ~6-7 steps
  over 10^7 steps; `bbtools.cycles` (k = 4) finds no linear cycle in 10^7 steps; CTL windows up to 8 cells do not close (group scan).

## Later

- Look for an invariant (a regular language of tapes, or a weighted count) that excludes the halting pattern;
  try CTL with word-based windows (the tape is made of a few words) instead of fixed cell windows.

## First look

Growth class **fixed/fixed** (left: fixed, exponent 0.057; right: fixed,
exponent 0.049). After 1,000,000,000 steps: 192 cells visited (154 left of the
start, 37 right), 83 ones.

## Pages

- [`pages/holdouts/1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LA---/explainer.html`](../../pages/holdouts/1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LA---/explainer.html)
- [`pages/holdouts/1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LA---/proof-status.html`](../../pages/holdouts/1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LA---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LA---/lean/check.sh
```
