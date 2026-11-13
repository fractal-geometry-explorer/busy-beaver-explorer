# 1RB0LE_1RC0RE_1RD0RA_1RE1LC_0LA0RF_1LE---

bbchallenge id 48565, group G08. Whether it halts from blank tape is **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 1RC | 0RE |
| C | 1RD | 0RA |
| D | 1RE | 1LC |
| E | 0LA | 0RF |
| F | 1LE | --- |

## What it does

The mirror image of the dense/sparse translators (like `1RB---_0RC0LA_1LD0RB_1LE1LD_1LF0LC_1LB1RE`): at the right
end the tape is dense, blocks `1^(4j+3)` separated by single 0s; at the left end it is sparse, the words `01`,
`0001`, `00`. Going left, E with a 0 ahead turns each `11` into `10` (`left_E`); going right, A turns each `0101`
into `1110` (`right_A`). The list of block lengths is scrambled on every round trip.

The machine halts only when F reads a 1: `E> 1 1` halts at once, `1 F> 0`, `B> 1 1 1` and `D> 0 1 1` after two
steps.

## What is proved, and where

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10⁴ steps (kernel) and 10⁷ (`native_decide`).
- `lean/Rules.lean` (kernel, written by `py/rules.py`): `left_E`, `right_A` and the halting situations.
- `py/turns.py` (heuristic): in the first 5·10⁶ steps, 273,318 of the 275,315 blocks strictly inside the dense
  tapes have length 4j+3.
- `c/visits.c` (trusted, our code): in the first 2·10⁸ steps the machine is in state F 22,449,902 times, always on a 0.

## What is open, next steps

The question itself, as for the whole dense/sparse family.

**Later**: set aside after the first pass.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LE_1RC0RE_1RD0RA_1RE1LC_0LA0RF_1LE---/lean/check.sh
python3 holdouts/1RB0LE_1RC0RE_1RD0RA_1RE1LC_0LA0RF_1LE---/py/rules.py     # rewrites lean/Rules.lean
python3 holdouts/1RB0LE_1RC0RE_1RD0RA_1RE1LC_0LA0RF_1LE---/py/turns.py 5e6 100
```
