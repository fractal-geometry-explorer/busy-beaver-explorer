# 1RB0LA_1LC0RD_0LD1LA_1LF0RE_1LB1RE_1RD---

bbchallenge id 34517.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LA |
| B | 1LC | 0RD |
| C | 0LD | 1LA |
| D | 1LF | 0RE |
| E | 1LB | 1RE |
| F | 1RD | --- |

## Status

**Open.** The macro structure below is read off long runs (heuristic: not yet stated as rules or proved); no
decision. Lean (`lean/Blank.lean`): no halt in 10^7 steps; C (`tools/c/triage.c`): none in 10^9.

## What it does

Near the left end the tape is `1^k (011111)^x 0^5 (111110)^y`, followed by a slowly growing stretch of debris (blocks
`1^5`, `1^10` separated by short runs of 0s, e.g. `0 1^5 0^4 1^10 0^3 1^5`). In each round trip the head moves one
six-cell word from the first block to the second, so x counts down while y counts up
(`(011111)^20 0^5 (111110)^4` → `(011111)^19 1^5 0^3 (111110)^5` → `(011111)^18 0^5 (111110)^7` → ...). When x reaches 0
the second block is rewritten into the first form, `(011111)^y`, a new transfer begins, and a few more debris blocks
are left at the boundary. Because every round trip crosses the whole block area, the tape grows like the square root
of the step count. The halt (F1) needs the transfer to meet a configuration it has not met in 10^9 steps.

## For later

State the transfer round (x, y) → (x − 1, y + 1) and the rewrite at x = 0 as symtm rules; then the open part is
the debris: whether its growth is regular (a counter) or can produce the halting pattern.

## First look

Growth class **fixed/sqrt** (left: sqrt, exponent 0.559; right: fixed,
exponent 0.0). After 1,000,000,000 steps: 49,566 cells visited (38,144 left of the
start, 32 right), 36,813 ones.

- left, step 978,042,165: `A>0 0 1^15 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0`
- left, step 993,753,162: `A>0 0 1^15 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0`

## Pages

- [`pages/holdouts/1RB0LA_1LC0RD_0LD1LA_1LF0RE_1LB1RE_1RD---/explainer.html`](../../pages/holdouts/1RB0LA_1LC0RD_0LD1LA_1LF0RE_1LB1RE_1RD---/explainer.html)
- [`pages/holdouts/1RB0LA_1LC0RD_0LD1LA_1LF0RE_1LB1RE_1RD---/proof-status.html`](../../pages/holdouts/1RB0LA_1LC0RD_0LD1LA_1LF0RE_1LB1RE_1RD---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LA_1LC0RD_0LD1LA_1LF0RE_1LB1RE_1RD---/lean/check.sh
```
