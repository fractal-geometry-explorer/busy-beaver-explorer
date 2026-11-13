# 1RB0LE_0RC1RA_1RD0RF_0LE1LD_1RA1LC_---0RE

bbchallenge id 160345. A BB(6) holdout, group G10 (one side of the tape grows like the square root of the step count, the other more slowly). Analysed by hand from the generated folder.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 0RC | 1RA |
| C | 1RD | 0RF |
| D | 0LE | 1LD |
| E | 1RA | 1LC |
| F | --- | 0RE |

## What it does

**Left part.** A long run of the period-3 word `100` (written `011`, `101` after leftward sweeps). The sweeps over
it, both directions, are proved shift rules (`lean/Rules.lean`).

**Right part: levels of blocks.** Blocks `1^(6k+1)` separated by `00`, sorted by length. The right end at step
372,052,921:

```
(100)^1560 (111001111)^503 1^7 00 1^13 00 1^13 00 ... 1^13 00 1^7 00100 1^17 00 1^19 00 1^19 00 ...
```

At step 370,082,314 (width 18,974): `(100)^1520`, then 502 blocks of 7, 306 of 13, 97 of 19, 59 of 25, 19 of 31,
11 of 37, 4 of 43, 2 of 49, the levels separated by single blocks of other lengths (11, 17, 23, ...). The counts fall
roughly geometrically: a counter-like hierarchy.

## Halting

F0 is the only halting transition, reached as `C>1 0`. It cannot happen inside the `100` part; whether the right
part ever produces it is open.

## What is proved

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10^4 steps (kernel) and 10^7 (`native_decide`).
- `lean/Rules.lean` (from `py/rules.py`, kernel): the four sweep rules over the left part (`e_left`, `d_left`, `a_right`, `b_right`).
- Computed (`tools/c/triage.c`): no halt in 10^9 steps.

Everything else on this page is heuristic: read off runs of up to 2·10^9 steps (`tools/c/tokrun.c`), not proved.

## For later

- Write the sweep over one block `1^(6k+1) 00` as a rule (both directions), then find what turns a block of level k
  into level k+1: that would give the counter explicitly and its carry rule.

## Reproduce

```sh
python3 holdouts/1RB0LE_0RC1RA_1RD0RF_0LE1LD_1RA1LC_---0RE/py/rules.py | diff - holdouts/1RB0LE_0RC1RA_1RD0RF_0LE1LD_1RA1LC_---0RE/lean/Rules.lean   # the rules file is current
gcc -O2 -o tokrun tools/c/tokrun.c
./tokrun 1RB0LE_0RC1RA_1RD0RF_0LE1LD_1RA1LC_---0RE 400000000 x=0 LR 2000 | tail -4   # the tape each time the head extends it (x is a 0)
```

## Pages

- [`pages/holdouts/1RB0LE_0RC1RA_1RD0RF_0LE1LD_1RA1LC_---0RE/explainer.html`](../../pages/holdouts/1RB0LE_0RC1RA_1RD0RF_0LE1LD_1RA1LC_---0RE/explainer.html)
- [`pages/holdouts/1RB0LE_0RC1RA_1RD0RF_0LE1LD_1RA1LC_---0RE/proof-status.html`](../../pages/holdouts/1RB0LE_0RC1RA_1RD0RF_0LE1LD_1RA1LC_---0RE/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LE_0RC1RA_1RD0RF_0LE1LD_1RA1LC_---0RE/lean/check.sh
```
