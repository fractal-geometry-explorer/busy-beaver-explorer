# 1RB0LB_1RC1LE_1LD0RF_---1LB_0LA0LC_1LB1RA

bbchallenge id 154458, group G08. Whether it halts from blank tape is **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LB |
| B | 1RC | 1LE |
| C | 1LD | 0RF |
| D | --- | 1LB |
| E | 0LA | 0LC |
| F | 1LB | 1RA |

## What it does

A two-sided bouncer. The background of the tape is the alternating word `1010…`, broken every few cells by a
defect (`00`, `11`, `111`, …). The sweeps carry the background past the head (A with a 1 behind it turns `01` into
`10`; B with `11` ahead turns `0101` into `1010`) and rearrange the defects, which show no visible order.

The machine halts only when D reads a 0; D is entered from C reading a 0, so `0 C> 0` halts, and so do
`0 0 E> 1`, `0 0 1 B> 1` and `0 0 A> 0 1` a few steps later.

## What is proved, and where

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10⁴ steps (kernel) and 10⁷ (`native_decide`).
- `lean/Rules.lean` (kernel, written by `py/rules.py`): the two crossings of the background (`walk_A`, `walk_B`)
  and the halting situations (`halt_C`, `halt_E`, `halt_B`, `halt_A`).
- `c/visits.c` (trusted, our code): in the first 2·10⁸ steps the machine is in state D 7,101,514 times, always on a 1.

## What is open, next steps

The question itself; no macro structure for the defects is known.

**Later**: set aside after the first pass.

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: E with 0 two left, 0 left, 1 under the head.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LB_1RC1LE_1LD0RF_---1LB_0LA0LC_1LB1RA/lean/check.sh
python3 holdouts/1RB0LB_1RC1LE_1LD0RF_---1LB_0LA0LC_1LB1RA/py/rules.py     # rewrites lean/Rules.lean
python3 holdouts/1RB0LB_1RC1LE_1LD0RF_---1LB_0LA0LC_1LB1RA/py/turns.py 3e6 50
```
