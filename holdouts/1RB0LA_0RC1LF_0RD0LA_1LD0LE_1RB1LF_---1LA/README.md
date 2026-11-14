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

## Deciders tried (F11, 13 November 2026)

None closes. Each reaches a halting configuration in its abstraction, which says nothing about halting.

- n-gram CPS (`tools/c/ngramcps.c`), equal widths on both sides: a halting local configuration is reached with plain up to width 20, history 1 up to width 20, history 2 up to width 18, history 3 up to width 15, LRU history up to width 7 (larger widths ran out of the 150 s or 60 million configuration budget).
- n-gram CPS with every cell tagged by its position mod p: fails for p = 2 up to width 16, p = 3 up to width 16, p = 4 up to width 16, p = 6 up to width 16.
- n-gram CPS where each side also carries the state of a small automaton that has read that side from the far end (every automaton with up to 3 states on both sides, or 4 states on one side), with position mod 1..4 and widths 4, 6, 8: no closed set without a halt in all 120 parameter sets.
- Run-length windows (the K nearest runs of equal macro cells on each side, run lengths kept exactly below T and mod M above): fails for all 72 parameter sets (cells of 1 to 4 bits, K = 2, 4, 6, T = 2, 4, M = 1, 2, 4).
- Two-automaton closed tape language by SAT (a deterministic automaton reading each side inward, n states each, CaDiCaL): no solution for n = 2..8; n = 9 not finished in 150 s.

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: D with 0 two left, 1 left, 1 under the head.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LA_0RC1LF_0RD0LA_1LD0LE_1RB1LF_---1LA/lean/check.sh
python3 holdouts/1RB0LA_0RC1LF_0RD0LA_1LD0LE_1RB1LF_---1LA/py/rules.py     # rewrites lean/Rules.lean
python3 holdouts/1RB0LA_0RC1LF_0RD0LA_1LD0LE_1RB1LF_---1LA/py/turns.py 3e6 50
```
