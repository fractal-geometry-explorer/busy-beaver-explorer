# 1RB0LE_1LC0RA_1RD0RC_1LA0LD_1LB0LF_1LC---

bbchallenge id 69718, group G08. Whether it halts from blank tape is **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 1LC | 0RA |
| C | 1RD | 0RC |
| D | 1LA | 0LD |
| E | 1LB | 0LF |
| F | 1LC | --- |

## What it does

A two-sided bouncer. At the left end the tape is a mix of runs of the word `001011` and short blocks like
`000 10 11 0 11 0 11`; at the right end it is stretches of `1010…` separated by `00`. C erases blocks of 1s going
right and D erases them going left; the rest of each sweep is irregular, and the mixture of words shows no order.

The machine halts only when F reads a 1; F is entered from E reading a 1, so `1 E> 1` halts, and `1 1 A> 1`,
`1 1 1 D> 0`, `1 1 C> 0 0` lead there.

## What is proved, and where

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10⁴ steps (kernel) and 10⁷ (`native_decide`).
- `lean/Rules.lean` (kernel, written by `py/rules.py`): `erase_C`, `erase_D` and the halting situations.
- `c/visits.c` (trusted, our code): in the first 2·10⁸ steps the machine is in state F 111,044 times, always on a 0.

## What is open, next steps

The question itself; no macro structure is known.

**Later**: set aside after the first pass.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LE_1LC0RA_1RD0RC_1LA0LD_1LB0LF_1LC---/lean/check.sh
python3 holdouts/1RB0LE_1LC0RA_1RD0RC_1LA0LD_1LB0LF_1LC---/py/rules.py     # rewrites lean/Rules.lean
python3 holdouts/1RB0LE_1LC0RA_1RD0RC_1LA0LD_1LB0LF_1LC---/py/turns.py 3e6 50
```
