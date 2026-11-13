# 1RB0RD_1RC1LE_1LD---_1RF0LE_1LD1LE_1RA0RF

bbchallenge id 173888. A BB(6) holdout, group G10 (one side of the tape grows like the square root of the step count, the other more slowly). Analysed by hand from the generated folder.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RD |
| B | 1RC | 1LE |
| C | 1LD | --- |
| D | 1RF | 0LE |
| E | 1LD | 1LE |
| F | 1RA | 0RF |

## What it does

The background is the pair `10`; the leftward sweep over it is a proved shift rule. Many short walls (`1`, `0`,
`000`, `0000`, phase changes) split it into domains. The right end at step 398,057,107 (width 23,283):

```
1 (10)^5 (01)^5205 (10)^3 1 (10)^3 000 (10)^1301 1 (10)^18 1 (10)^61 (01)^8 (10)^1129 1 (10)^79 (01)^495
(10)^20 (01)^556 (10)^54 1 (10)^411 (01)^58 0000 (10)^118 (01)^122 0 (01)^76 (10)^143 000 (10)^87 ...
... 0010100 (101101010101)^5 00101 (10)^3 1 (10)^3 000 10100101 (10)^5 0101 0000 10100101 (10)^4 1101 (10)^5 (0101000)^3
```

The domains shrink from the left end to the right roughly by halves; the right end is a dense mix of short pieces.
`1RB1LC_1RC---_1LD1LC_1RE0LC_1RF0RE_1RA0RD` (same batch) looks similar.

## Halting

C1 is the only halting transition, reached as `B>0 1`. It cannot happen inside a domain; whether a wall ever
produces it is open.

## What is proved

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10^4 steps (kernel) and 10^7 (`native_decide`).
- `lean/Rules.lean` (from `py/rules.py`, kernel): the leftward sweep over `10` in both phases (`d_left`, `e_left`).
- Computed (`tools/c/triage.c`): no halt in 10^9 steps.

Everything else on this page is heuristic: read off runs of up to 2·10^9 steps (`tools/c/tokrun.c`), not proved.

## For later

- Classify the wall types and write a sweep across each as a rule; then look for a recursive (counter-like)
  structure in the domain lengths, which the halving suggests.

## Reproduce

```sh
python3 holdouts/1RB0RD_1RC1LE_1LD---_1RF0LE_1LD1LE_1RA0RF/py/rules.py | diff - holdouts/1RB0RD_1RC1LE_1LD---_1RF0LE_1LD1LE_1RA0RF/lean/Rules.lean   # the rules file is current
gcc -O2 -o tokrun tools/c/tokrun.c
./tokrun 1RB0RD_1RC1LE_1LD---_1RF0LE_1LD1LE_1RA0RF 400000000 x=0 LR 2000 | tail -4   # the tape each time the head extends it (x is a 0)
```

## Pages

- [`pages/holdouts/1RB0RD_1RC1LE_1LD---_1RF0LE_1LD1LE_1RA0RF/explainer.html`](../../pages/holdouts/1RB0RD_1RC1LE_1LD---_1RF0LE_1LD1LE_1RA0RF/explainer.html)
- [`pages/holdouts/1RB0RD_1RC1LE_1LD---_1RF0LE_1LD1LE_1RA0RF/proof-status.html`](../../pages/holdouts/1RB0RD_1RC1LE_1LD---_1RF0LE_1LD1LE_1RA0RF/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RD_1RC1LE_1LD---_1RF0LE_1LD1LE_1RA0RF/lean/check.sh
```
