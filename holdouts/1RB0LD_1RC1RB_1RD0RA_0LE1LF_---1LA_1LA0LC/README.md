# 1RB0LD_1RC1RB_1RD0RA_0LE1LF_---1LA_1LA0LC

bbchallenge id 21414, group G08. Whether it halts from blank tape is **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LD |
| B | 1RC | 1RB |
| C | 1RD | 0RA |
| D | 0LE | 1LF |
| E | --- | 1LA |
| F | 1LA | 0LC |

## What it does

A two-sided bouncer. At the left end the tape reads `(01)^k₁ 1 (01)^k₂ 1 (01)^k₃ …`: a list of numbers k, most
of them odd (3 is the most common), with rare defects such as `10100`. Going right, B turns each `1010` into `1101`,
so at the right end the list is written in the words `1110`, `1101`, `1011`, `0111`; going left, D turns `1101`
back into `0101`. The far part of the list is carried along almost unchanged, but near the left end the stretches
merge and split irregularly from trip to trip.

The machine halts only when E reads a 0; E is entered from D reading a 0, so `0 D> 0` halts, and `0 0 A> 1`,
`0 C> 1 1` lead there.

## What is proved, and where

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10⁴ steps (kernel) and 10⁷ (`native_decide`).
- `lean/Rules.lean` (kernel, written by `py/rules.py`): the two sweeps (`right_B`, `left_D`) and the halting
  situations (`halt_D`, `halt_A`, `halt_C`).
- `c/visits.c` (trusted, our code): in the first 2·10⁸ steps the machine is in state E 17,398,306 times, always on a 1.

## What is open, next steps

The question itself. A description of how the list changes at its left end (which numbers merge, which split)
would be the first step; it looks irregular.

**Later**: set aside after the first pass.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LD_1RC1RB_1RD0RA_0LE1LF_---1LA_1LA0LC/lean/check.sh
python3 holdouts/1RB0LD_1RC1RB_1RD0RA_0LE1LF_---1LA_1LA0LC/py/rules.py     # rewrites lean/Rules.lean
python3 holdouts/1RB0LD_1RC1RB_1RD0RA_0LE1LF_---1LA_1LA0LC/py/turns.py 3e6 50   # the list at the left end
```
