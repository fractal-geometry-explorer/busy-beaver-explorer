# 1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA

bbchallenge id 163738, group G08. Whether it halts from blank tape is **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LD |
| B | 0RC | 0RF |
| C | 1LD | 0RB |
| D | 1LE | --- |
| E | 0LA | 0LB |
| F | 0LE | 0RA |

## What it does

A counter machine in disguise. At the left end the tape is a handful of long blocks of 1s, e.g.
`A> 000 1^3 00 1^x 00 1^7 000 1^y 0001000 1^z`. Going right, C packs every `1111` into `1000` (`pack`); going left, E
unpacks every `0001` back into `1111` (`unpack`). One round trip changes the counts by fixed amounts (here x − 8,
y − 8, z + 32; in other epochs x − 12, y − 4, z + 32, or x − 8, z + 24 with a fixed `(1000)^2` in front). When a
count runs out the blocks are rearranged and a new epoch starts with larger counts: the epochs of the first 6·10⁶
steps start with a block of 285, 851, 1,145 and 1,553 ones.

The machine halts only when D reads a 1; `1 A> 1` and `1 C> 0` halt at once, `1 1 E> 0` after two steps.

## What is proved, and where

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10⁴ steps (kernel) and 10⁷ (`native_decide`).
- `lean/Rules.lean` (kernel, written by `py/rules.py`): `pack`, `unpack`, and the halting situations `halt_A`,
  `halt_C`, `halt_E`.
- `py/turns.py` (heuristic): the counters at every left turn (`python3 py/turns.py 1e7 | grep ' L  A> 000 '`).
- `c/visits.c` (trusted, our code): in the first 2·10⁸ steps the machine is in state D 26,324,186 times, always on a 0.

## What is open, next steps

The question itself. This is the most promising of the chaotic-looking part of the group: within an epoch the
counts move linearly, so each epoch's round trip is a symbolic rule that symtm can prove, and the epoch changes are
finitely many shapes. Next: list the epoch shapes, prove each round trip as a rule with the counts as variables, and
check that every epoch change leads to another listed shape (the same plan as for
`1RB0LF_1LC0LA_1RA0RD_---1RE_1LA1RC_0LB0RC`).

**Later**: not attempted beyond the first pass.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA/lean/check.sh
python3 holdouts/1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA/py/rules.py     # rewrites lean/Rules.lean
python3 holdouts/1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA/py/turns.py 1e7 | grep ' L  A> 000 '   # the counters at each left turn
```
