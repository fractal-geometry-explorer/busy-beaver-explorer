# 1RB1LE_1LC1RE_1LE1LD_1LC0LA_1RF0LA_---0RA

bbchallenge id 144438. A BB(6) holdout, group G10 (one side of the tape grows like the square root of the step count, the other more slowly). Analysed by hand from the generated folder.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LE |
| B | 1LC | 1RE |
| C | 1LE | 1LD |
| D | 1LC | 0LA |
| E | 1RF | 0LA |
| F | --- | 0RA |

## What it does

The tape repeats `111110` in different rotations; the walls between domains are phase shifts. The leftward sweeps
over the rotations are proved shift rules. Two end turns:

```
step 366,599,956  right end  (111110)^4096 (111011)^769 (101111)^168 10 (111011)^4285 (101111)^308 10 (111011)^818 1100
step 366,683,522  left end   0 (01)^3 (110101)^4095 1 (101110)^769 (111010)^168 111 (011101)^4285 (110101)^308 1 (101110)^818 1111
step 1,663,363,604 right end (111110)^4096 (111011)^797 (101111)^12372 10 (111011)^3933 (101111)^196 10 (111011)^782 1100
```

The right end is visited rarely (325 times in 2·10^9 steps). Between consecutive visits late in the run the width
grows by 1024, the first domain by 1536, and the next domains change by −384, −96, −24, −6 (ratio 4): a
base-4-counter-like hierarchy.

## Halting

F0 is the only halting transition, reached as `E>0 0`. The background has no `00`; only the ends do. Whether the
counter ever brings E onto them in the wrong phase is open.

## What is proved

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10^4 steps (kernel) and 10^7 (`native_decide`).
- `lean/Rules.lean` (from `py/rules.py`, kernel): the four leftward sweep rules (`e_left`, `a_left`, `d_left`, `c_left`).
- Computed (`tools/c/triage.c`): no halt in 10^9 steps.

Everything else on this page is heuristic: read off runs of up to 2·10^9 steps (`tools/c/tokrun.c`), not proved.

## For later

- Write the rule for one visit of the right end (the walls and the changes −384, −96, ... as functions of the
  domain lengths); the ratio-4 pattern suggests an exact base-4 counter that might be proved nonhalting by
  induction.

## Reproduce

```sh
python3 holdouts/1RB1LE_1LC1RE_1LE1LD_1LC0LA_1RF0LA_---0RA/py/rules.py | diff - holdouts/1RB1LE_1LC1RE_1LE1LD_1LC0LA_1RF0LA_---0RA/lean/Rules.lean   # the rules file is current
gcc -O2 -o tokrun tools/c/tokrun.c
./tokrun 1RB1LE_1LC1RE_1LE1LD_1LC0LA_1RF0LA_---0RA 400000000 x=0 LR 2000 | tail -4   # the tape each time the head extends it (x is a 0)
```

## Deep exact run

No halt in the first 7.19x10^18 steps: the macro simulator `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/c/msim.c` with blocks of 6 cells ran
from blank tape to step 7,191,166,652,716,873,648. It is exact, and at this block size it agrees with the
direct simulator after 2,000,036,035 steps (`python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/deep.py run 240`, then `verify`).

## Pages

- [`pages/holdouts/1RB1LE_1LC1RE_1LE1LD_1LC0LA_1RF0LA_---0RA/explainer.html`](../../pages/holdouts/1RB1LE_1LC1RE_1LE1LD_1LC0LA_1RF0LA_---0RA/explainer.html)
- [`pages/holdouts/1RB1LE_1LC1RE_1LE1LD_1LC0LA_1RF0LA_---0RA/proof-status.html`](../../pages/holdouts/1RB1LE_1LC1RE_1LE1LD_1LC0LA_1RF0LA_---0RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LE_1LC1RE_1LE1LD_1LC0LA_1RF0LA_---0RA/lean/check.sh
```
