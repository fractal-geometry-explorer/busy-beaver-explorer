# 1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LB---

bbchallenge id 55861.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 1LC | 0RE |
| C | 1RF | 1LD |
| D | 1LA | 0LB |
| E | 1RD | 1RA |
| F | 1LB | --- |

## Status

**Open.** The macro structure below is read off long runs (heuristic: not yet stated as rules or proved); no
decision. Lean (`lean/Blank.lean`): no halt in 10^7 steps; C (`tools/c/triage.c`): none in 10^9.

## What it does

Late in the run, at the left-end visits, the tape is `A>0 (11010)^x (110)^3 (10110101)^y [10 1^3 0 | 100] 1^z ...`
with a fixed tail. Every two visits y drops by 1 while x grows by 2 and z by 2 (`(11010)^402 ... (10110101)^217 ...
1^529` → `(11010)^404 ... (10110101)^216 ... 1^531`). When the middle block is used up the tape is rebuilt: the first
block becomes `(10110)^n`, a run of `(101)^3 0110` units appears, and a new middle block starts. So it is a three-counter
machine with periodic resets, the counts growing from reset to reset (z: 126, 130, 178, 266, 339, ..., 541). The halt
is F1.

## For later

Write the round (x, y, z) → (x + 2, y − 1, z + 2) and the reset as rules; the reset map on the counts is the
part to understand (it may be Collatz-like).

## First look

Growth class **fixed/sqrt** (left: sqrt, exponent 0.506; right: fixed,
exponent 0.037). After 1,000,000,000 steps: 25,612 cells visited (18,770 left of the
start, 61 right), 15,549 ones.

- left, step 971,131,343: `C>0 0 1^2 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 `
- left, step 986,816,021: `C>0 0 1^2 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 `

## Pages

- [`pages/holdouts/1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LB---/explainer.html`](../../pages/holdouts/1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LB---/explainer.html)
- [`pages/holdouts/1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LB---/proof-status.html`](../../pages/holdouts/1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LB---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LB---/lean/check.sh
```
