# 1RB0LB_1RC0LD_0LA1RD_1LC1LE_1LF0RE_1LD---

Group G08 (two-sided square-root growth). Whether it halts from blank tape is **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LB |
| B | 1RC | 0LD |
| C | 0LA | 1RD |
| D | 1LC | 1LE |
| E | 1LF | 0RE |
| F | 1LD | --- |

## What it does

Two regular regions grow on either side of an irregular boundary where the head works. On the left a 26-cell word

    w = 1111 000 1 000 1 000 111111 0 1 000

is repeated: at the moments the head reaches a new cell on the left the tape starts `0 1 000 w^n …`, with n = 12 at
step 1,010,877, 14 at 1,186,572 and 20 at 1,927,963 (`py/turns.py`). On the right the tape is a finer pattern of
blocks `1000`, `11`, `11111` separated by `00`. The head never sweeps the whole tape: it works in zig-zags of 50 to
100 cells near the boundary and now and then runs out to an end to add a cell. Its fast moves: E moving right erases
a run of 1s (`erase`), D moving left fills each `100` into `111` (`fill`).

The only halt is F reading a 1. F is entered only from E reading a 0, so `1 0 D> 1` halts (`halt_D`). In the first
2·10⁶ steps D reads a 1 233,188 times and never with `1 0` to its left; F always reads a 0 (`py/near_halt.py`).

## What is proved, and where

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10⁴ steps (kernel) and 10⁷ (`native_decide`).
- `lean/Rules.lean` (kernel, written by `py/rules.py`): `erase`, `fill` for any length; `halt_D`.
- `lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, every configuration two steps before a
  halt is `1 0 D> 1`.
- `py/turns.py`, `py/near_halt.py` (heuristic): the tape as words at the end turns; the contexts of the states next to
  the halt.

## What is open, next steps

How the boundary region turns right-hand material into copies of w (the macro rule of the zig-zag), and an invariant
of it that keeps `1 0` away from D's left. The boundary is only a few dozen cells wide, so a closed tape language
with the two periodic regions as automaton loops is the natural thing to try.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LB_1RC0LD_0LA1RD_1LC1LE_1LF0RE_1LD---/lean/check.sh
python3 holdouts/1RB0LB_1RC0LD_0LA1RD_1LC1LE_1LF0RE_1LD---/py/route.py        # rewrites lean/Route.lean
python3 holdouts/1RB0LB_1RC0LD_0LA1RD_1LC1LE_1LF0RE_1LD---/py/rules.py         # rewrites lean/Rules.lean
python3 holdouts/1RB0LB_1RC0LD_0LA1RD_1LC1LE_1LF0RE_1LD---/py/turns.py 2e6 L   # the left end, as copies of w
python3 holdouts/1RB0LB_1RC0LD_0LA1RD_1LC1LE_1LF0RE_1LD---/py/near_halt.py 1e6
```
