# 1RB0LC_1LC0RE_1RA1LD_1LA1LC_1RF0RA_---0LA

bbchallenge id 149962, group G08. Whether it halts from blank tape is **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 1LC | 0RE |
| C | 1RA | 1LD |
| D | 1LA | 1LC |
| E | 1RF | 0RA |
| F | --- | 0LA |

## What it does

A two-sided bouncer over a tape made of the words `011`, `110`, `100`, `01` and blocks of 1s, in no visible
order. Going right, A turns `011` into `100`; going left, C with a 1 ahead turns `110` into `011` and passes `01`
unchanged.

The machine halts only when F reads a 0; F is entered from E reading a 0, so `E> 0 0` halts, and `B> 1 0 0` and
`A> 0 1 0 0` lead there.

## What is proved, and where

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10⁴ steps (kernel) and 10⁷ (`native_decide`).
- `lean/Rules.lean` (kernel, written by `py/rules.py`): `walk_A`, `walk_C01`, `walk_C110`, and the halting
  situations `halt_E`, `halt_B`, `halt_A`.
- `c/visits.c` (trusted, our code): in the first 2·10⁸ steps the machine is in state F 5,702,121 times, always on a 1.

## What is open, next steps

The question itself; no macro structure is known.

**Later**: set aside after the first pass.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LC_1LC0RE_1RA1LD_1LA1LC_1RF0RA_---0LA/lean/check.sh
python3 holdouts/1RB0LC_1LC0RE_1RA1LD_1LA1LC_1RF0RA_---0LA/py/rules.py     # rewrites lean/Rules.lean
python3 holdouts/1RB0LC_1LC0RE_1RA1LD_1LA1LC_1RF0RA_---0LA/py/turns.py 3e6 50
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_---0RC`](../1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_---0RC/README.md): rename A→C, B→A, C→B, D→D, E→E, F→F and exchange left and right; it is this table started in state B, in a mirror
- [`1RB1LD_1RC0LA_1LA0RE_1LB1LA_1RF0RB_---0LB`](../1RB1LD_1RC0LA_1LA0RE_1LB1LA_1RF0RB_---0LB/README.md): rename A→B, B→C, C→A, D→D, E→E, F→F; it is this table started in state C

<!-- end of related machines -->
