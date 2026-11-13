# 1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---

bbchallenge id 9516. One of the six-state holdouts whose halting from blank tape is open. Family: **solid block and alternating stretch, erratic sizes**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 1LC | 1RA |
| C | 1RA | 1LD |
| D | 0LC | 0LA |
| E | 0RE | 1RF |
| F | 0RC | --- |

## Status

Open. Lean: only the generated files (halting configurations; no halt in 10^4 steps by the kernel, 10^7 by
`native_decide`). C: no halt in 10^9 steps.

## What it does

Two parts: at left-end switches `0 0 (10)^r 1^m` (or `0 1 1 (10)^r 1^m`), at right-end switches `0 1^m (10)^r 0`;
the parts swap sides each trip, with erratic sizes (e.g. right m = 2733, 3627, 238 after left m = 9, 1564).

Halting: F on a 1, entered only from E on a 1 moving right: a halt is exactly `E>1 1`.

Growth: 666 side switches in 10^9 steps; after 5·10^8 they are ≈ 0.291·w² steps apart and add ≈ 6 cells each, so
width ~ t^(1/3) (fitted 0.344; 3,679 cells). `py/shape.py` and `py/switches.py` print all of this from a `tmrun ... records` log.

## Later

1. Find the rule that maps one side switch to the next (sizes of the runs), as was done for the hole-wandering
   machines of this group (e.g. `1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_0RA0LA`), and prove its pieces with `bbtools.symtm`.
2. Show that the halting pattern can never arise from the shapes seen.

## First look

Growth class **power/power** (left: power, exponent 0.341; right: power,
exponent 0.345). After 1,000,000,000 steps: 3,680 cells visited (1,766 left of the
start, 1,213 right), 3,050 ones.

- left, step 980,492,457: `E>0 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `
- left, step 996,727,782: `C>0 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- right, step 972,250,598: `0 1^1438 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1`
- right, step 996,613,780: `0 1^239 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `

## Pages

- [`pages/holdouts/1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---/explainer.html`](../../pages/holdouts/1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---/explainer.html)
- [`pages/holdouts/1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---/proof-status.html`](../../pages/holdouts/1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---/lean/check.sh
gcc -O2 -o /tmp/tmrun tools/c/tmrun.c && /tmp/tmrun 1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC--- 1000000000 records 100000 > /tmp/rec.txt
python3 holdouts/1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---/py/shape.py /tmp/rec.txt a=10
python3 holdouts/1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---/py/switches.py /tmp/rec.txt a=10
```
