# 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1RF

Group G08 (two-sided square-root growth). Whether it halts from blank tape is **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 1RC | 1RA |
| C | 1RD | 0RF |
| D | 0LE | --- |
| E | 1LA | 1LE |
| F | 0RA | 1RF |

## What it does

Full sweeps over a row of periodic regions. With `c = 110`, `q = 010110101101010110101101` (24 cells) and
`s = 101010110110110` (15 cells), at the left-end turn of step 7,087,597 the tape is (`X = 10`)

    B> c^2 0 c^2 X c X c 1 q^40 0 X c X c X^2 c X^3 c^2 X c X s^36 X c^6 X s c X^5 s c X^16 s c X^38 c X c X^78
       c^2 0 c^2 X^157 1 c^3 ... (1 0 1 c^3)^many ... irregular right end

The runs of `10` roughly double in length (5, 16, 38, 78, 157). Counting copies at the left-end turns: the q-run
grows from 3 (step 561,704) to 111 (step 4,263,440) while the s-run shrinks from 50 to 7; by 4.7·10⁶ both are gone
and q starts again; from 5.9·10⁶ to 1.2·10⁷ an s-run of 35–36 copies sits still while q grows to 109 and the region
of `101110110110` further right shrinks. It looks like a counter whose digits are whole regions.

Passes (proved for any n): A moving right rewrites q (rotation `011010110101011010110101`) as
`100111001111100111001111`, 32 steps a copy (`pass_right_q`); C moving left restores it, 68 steps a copy
(`pass_left_q`); A turns each `011` into `100` (`pass_right_c`). These need `set_option maxRecDepth`.

The only halt is D reading a 1, and D is entered only from C reading a 0: `C> 0 1` halts (`halt_C`).

## What is proved, and where

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10⁴ steps (kernel) and 10⁷ (`native_decide`).
- `lean/Rules.lean` (kernel, written by `py/rules.py`): `pass_right_q`, `pass_left_q`, `pass_right_c`; `halt_C`.
- `lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, every configuration two steps before a
  halt is `B> 0 0 1`.
- `py/turns.py` (heuristic): the tape as words at the end turns.

## What is open, next steps

The round-trip rule on the row of regions (which region feeds which, and the rebuild when one runs out), then an
invariant from it that keeps D off a 1. The doubling runs of `10` suggest the digits of a binary-like counter.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1RF/lean/check.sh
python3 holdouts/1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1RF/py/route.py        # rewrites lean/Route.lean
python3 holdouts/1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1RF/py/rules.py        # rewrites lean/Rules.lean
python3 holdouts/1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1RF/py/turns.py 1.2e7 L  # the tape at the left-end turns
```
