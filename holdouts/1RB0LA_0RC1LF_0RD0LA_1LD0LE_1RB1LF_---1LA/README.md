# 1RB0LA_0RC1LF_0RD0LA_1LD0LE_1RB1LF_---1LA

bbchallenge id 45336, group G08. Whether it halts from blank tape is **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LA |
| B | 0RC | 1LF |
| C | 0RD | 0LA |
| D | 1LD | 0LE |
| E | 1RB | 1LF |
| F | --- | 1LA |

## What it does

The tape is a list of short blocks of 1s (lengths 2 to 7) separated by single 0s, with some runs of the words
`0111` and `1110`. The head does not simply sweep: it zig-zags, for example moving left 8 cells every 44 steps while
it rewrites the blocks it passes, and the right end advances 8 cells at a time (both ends grow like the square root
of the step count). The block lengths look random.

The machine halts only when F reads a 0. F is entered from B or E reading a 1 and moving left, so `0 B> 1` and
`0 E> 1` halt at once, and `0 1 1 D> 0` after three steps.

## What is proved, and where

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10⁴ steps (kernel) and 10⁷ (`native_decide`).
- `lean/Rules.lean` (kernel, written by `py/rules.py`): C carrying a 0 through a block of 1s (`walk_ones`), C on
  runs of `0111` (`shift_0111`), and the halting situations (`halt_B`, `halt_E`, `halt_D`).
- `c/visits.c` (trusted, our code): in the first 2·10⁸ steps the machine is in state F 9,297,309 times, always on a 1.

## What is open, next steps

The question itself; no macro structure is known. NGramCPS (n ≤ 10) and window CTL (K ≤ 7) leave it open.

**Later**: set aside after the first pass.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LA_0RC1LF_0RD0LA_1LD0LE_1RB1LF_---1LA/lean/check.sh
python3 holdouts/1RB0LA_0RC1LF_0RD0LA_1LD0LE_1RB1LF_---1LA/py/rules.py     # rewrites lean/Rules.lean
python3 holdouts/1RB0LA_0RC1LF_0RD0LA_1LD0LE_1RB1LF_---1LA/py/turns.py 3e6 50
```
