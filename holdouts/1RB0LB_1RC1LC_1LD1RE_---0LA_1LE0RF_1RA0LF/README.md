# 1RB0LB_1RC1LC_1LD1RE_---0LA_1LE0RF_1RA0LF

bbchallenge id 111009.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LB |
| B | 1RC | 1LC |
| C | 1LD | 1RE |
| D | --- | 0LA |
| E | 1LE | 0RF |
| F | 1RA | 0LF |

## Status

**Open.** The macro structure below is read off long runs (heuristic: not yet stated as rules or proved); no
decision. Lean (`lean/Blank.lean`): no halt in 10^7 steps; C (`tools/c/triage.c`): none in 10^9.

## What it does

The two machines `1RB0LB_1RC1LC_1LD1RE_---0LA_1LE0RF_1RA0LF` and `1RB0LB_1RC1LC_1LD1RE_---0LA_1RE0RF_1RA0LF` differ only
in E0 (1LE or 1RE) and look alike. Next to the left end the tape is `(01)^4 (10101001)^n` followed by a long stretch
built from the words `10`, `01`, `0110`, `1001` (e.g. `(10)^10 010110100101 (10)^3 01100101100110 (1001)^3 ...`). The
block count n grows in long cycles, by about 50 per cycle (16, 65, 33, 82, 133, 183, ... at successive samples: it
also drops when a cycle restructures the boundary), and the stretch behind it changes only near its left end. The
halt is D0, reached only if the head reads a 0 in state D, which has not happened in 10^9 steps.

## For later

Find the cycle: what one long cycle does to n and to the boundary words; then whether the stretch behind is a
counter that can feed D a 0.

## First look

Growth class **fixed/sqrt** (left: sqrt, exponent 0.519; right: fixed,
exponent 0.037). After 1,000,000,000 steps: 19,947 cells visited (14,708 left of the
start, 1,070 right), 10,929 ones.

- left, step 972,080,027: `B>0 0^2 1 0 1 0 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 `
- left, step 987,886,051: `B>0 0^2 1 0 1 0 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 `

## Pages

- [`pages/holdouts/1RB0LB_1RC1LC_1LD1RE_---0LA_1LE0RF_1RA0LF/explainer.html`](../../pages/holdouts/1RB0LB_1RC1LC_1LD1RE_---0LA_1LE0RF_1RA0LF/explainer.html)
- [`pages/holdouts/1RB0LB_1RC1LC_1LD1RE_---0LA_1LE0RF_1RA0LF/proof-status.html`](../../pages/holdouts/1RB0LB_1RC1LC_1LD1RE_---0LA_1LE0RF_1RA0LF/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LB_1RC1LC_1LD1RE_---0LA_1LE0RF_1RA0LF/lean/check.sh
```
