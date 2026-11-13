# 1RB1LB_0RC0LD_1LD1RE_1RC0LA_1RD1RF_0RD---

bbchallenge id 119197. One of the six-state holdouts. Analyzed by hand (group G02), partly.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LB |
| B | 0RC | 0LD |
| C | 1LD | 1RE |
| D | 1RC | 0LA |
| E | 1RD | 1RF |
| F | 0RD | --- |

## What it does (observed)

The right part of the tape is two big blocks of ones (at 10^9 steps: `1 0 1^39 0 1^10903 0 1^37419 D>0`), the left
part a short word of `100`s. Each round trip of the head moves 3 ones out of the right block and 4 into the one
before; when the right block runs out a new regime starts, about 4/3 as long. Cycles per regime (from
`py/cycles_rules.py`): 3, 7, 12, 17, 25, 36, 49, 67, 89, 117, 159, 218, 290, 385, 511, ..., 6003, 8005, 10672,
14230, 18972, 25273, 33701, 44967, ... So this is a **Collatz-like map n -> ~4n/3**, the offset depending on n mod 3
and on the word at the left end.

## Lean

`lean/Cycles.lean` (from `py/cycles_rules.py`, `bbtools.cycles` with blocks of 3 cells): the 35 one-cycle rules
applied on the run to 10^15 steps, each a theorem for all values of its variables (e.g. `cycle23`: `(111)^n1` +8,
`(111)^n3` -6, 36·n3 + 198 steps). The file takes about 2 minutes to check.

## Halting

Only F1 halts. `python3 -m bbtools.cycles M 3 1e40` reaches 10^40 steps (145 jumps, 70 rules) with no halt.
n-gram CPS (widths 3..7) fails. Open.

## Notes for later

* Extract the end-of-regime map: (left word, n mod 3) -> (next left word, offset), as for
  `1RB0RF_1LC---_1RD0LC_0RE0RD_1LF1LC_1LE1RA` (the same shape of analysis: sample configurations at the regime
  ends, simulated for small n and extrapolated), then find which left words lead to F1.

## Pages

- [`pages/holdouts/1RB1LB_0RC0LD_1LD1RE_1RC0LA_1RD1RF_0RD---/explainer.html`](../../pages/holdouts/1RB1LB_0RC0LD_1LD1RE_1RC0LA_1RD1RF_0RD---/explainer.html)
- [`pages/holdouts/1RB1LB_0RC0LD_1LD1RE_1RC0LA_1RD1RF_0RD---/proof-status.html`](../../pages/holdouts/1RB1LB_0RC0LD_1LD1RE_1RC0LA_1RD1RF_0RD---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LB_0RC0LD_1LD1RE_1RC0LA_1RD1RF_0RD---/lean/check.sh
```
