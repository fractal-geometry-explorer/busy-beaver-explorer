# 1RB1LE_0RC0RB_1RD1RF_1LA0LE_0LD0LB_---0RD

bbchallenge id 65208. One of the six-state holdouts whose halting from blank tape is open. Its run looks chaotic on a tape that grows roughly logarithmically.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LE |
| B | 0RC | 0RB |
| C | 1RD | 1RF |
| D | 1LA | 0LE |
| E | 0LD | 0LB |
| F | --- | 0RD |

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`. C (`tools/c/tmrun.c`): no halt in 10,000,000,000 steps.

## What it does

The tape is a sequence of copies of <code>110</code> separated by short gaps (<code>0</code>, <code>000</code> or <code>1 00</code>), in no visible order, and the run keeps rewriting it. It grows on both sides, by about 100 cells per tenfold increase in time.

- **Growth.** Cells visited: 239 (10^6), 316 (10^7), 462 (10^8), 575 (10^9), 672 (10^10) steps.
- **Halting.** Only F0 halts; F is entered only from C1 (`1RF`), 5,555,291 times in 10^8 steps, always onto a 1.
- **No structure found.** `bbtools.macro` with blocks of 3 / 6 cells needs one macro step per ~3 / ~6-7 steps
  over 10^7 steps; `bbtools.cycles` (k = 4) finds no linear cycle in 10^7 steps; CTL windows up to 8 cells do not close (group scan).

## Later

- Look for an invariant (a regular language of tapes, or a weighted count) that excludes the halting pattern;
  try CTL with word-based windows (the tape is made of a few words) instead of fixed cell windows.

## First look

Growth class **fixed/power** (left: fixed, exponent 0.054; right: power,
exponent 0.16). After 1,000,000,000 steps: 576 cells visited (174 left of the
start, 393 right), 281 ones.

- right, step 547,646,528: `1 0^2 1^3 0^2 1^2 0^5 1^2 0 1 0^2 1^2 0^4 1^2 0^4 1^2 0^2 1^2 0^2 1^2 0^4 1^2 0^4 1^2 0 1 0^2 1^2 0 1 0^2 1^3 0^2 1^2 0^2 1^2 0 1 0^2 1^2 0 1 0^2 1^2 0^4 1^2 0^4 1^2 0 1 0^2 1^2 0^4 1^2 0^4 1^2 0 1 0^2 1^2 0 1 0^2 1^2 0 1 0^2 1^2 0 1 0^2 1^2 0^4 1^2 0^4 1^2 0 1 0^2 1^2 0^4 1^2 0^2 1^2 0 1 0^2 1^2 0 `
- right, step 909,086,150: `1 0^2 1^3 0^2 1^2 0^5 1^2 0 1 0^2 1^2 0^4 1^2 0^4 1^2 0^2 1^2 0^2 1^2 0^4 1^2 0^4 1^2 0 1 0^2 1^2 0 1 0^4 1^2 0^2 1 0^2 1^2 0^4 1^2 0 1 0^2 1^2 0^4 1^2 0 1 0^2 1^2 0 1 0^2 1^2 0^4 1^2 0^4 1^2 0 1 0^2 1^2 0 1 0^2 1^2 0 1 0^2 1^2 0 1 0^2 1^2 0 1 0^2 1^2 0 1 0^2 1^2 0^4 1^2 0^4 1^2 0^2 1^2 0^4 1^2 0^4 `

## Pages

- [`pages/holdouts/1RB1LE_0RC0RB_1RD1RF_1LA0LE_0LD0LB_---0RD/explainer.html`](../../pages/holdouts/1RB1LE_0RC0RB_1RD1RF_1LA0LE_0LD0LB_---0RD/explainer.html)
- [`pages/holdouts/1RB1LE_0RC0RB_1RD1RF_1LA0LE_0LD0LB_---0RD/proof-status.html`](../../pages/holdouts/1RB1LE_0RC0RB_1RD1RF_1LA0LE_0LD0LB_---0RD/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LE_0RC0RB_1RD1RF_1LA0LE_0LD0LB_---0RD/lean/check.sh
```
