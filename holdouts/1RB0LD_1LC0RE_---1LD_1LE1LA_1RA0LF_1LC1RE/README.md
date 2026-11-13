# 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE

Group G08 (two-sided square-root growth). Whether it halts from blank tape is **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LD |
| B | 1LC | 0RE |
| C | --- | 1LD |
| D | 1LE | 1LA |
| E | 1RA | 0LF |
| F | 1LC | 1RE |

## What it does

The tape is the alternating background `1010...` with defects (`11`, `111`, `1111`, `00`). At the left-end turn of
step 2,938,258 (`x` = 0):

    B> 1 x x 1 x 1 1 1 x 1 x 1 x 1 x 1 x 1 1 x 1 x 1 x 1 x 1 x 1 x 1 1 x 1 x 1 x 1 x 1 1 1 x 1 x x 1 ...

About one pair of neighbours in six is `11` and one in twenty-five is `00`, at every size (557 cells with 81 and 34
such pairs at step 324,106; 3,077 cells with 486 and 119 at step 9,176,284; `py/defects.py`). The head crosses the
tape in irregular zig-zags of tens to hundreds of cells; no repeating word, list of blocks or counter is visible.

Fast moves (proved for any n): A moving right turns `(0101)^n` into `(1101)^n` (`fill_A`), B turns `(1010)^n` into
`(1011)^n` (`fill_B`), eight steps a copy.

The only halt is C reading a 0. C is entered from B and F reading a 0, so `0 B> 0` and `0 F> 0` halt (`halt_B`,
`halt_F`); in the run there is always a 1 to their left then.

## What is proved, and where

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10⁴ steps (kernel) and 10⁷ (`native_decide`).
- `lean/Rules.lean` (kernel, written by `py/rules.py`): `fill_A`, `fill_B`; `halt_B`, `halt_F`.
- `lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, every configuration two steps before a
  halt is `0 0 E> 1` (so `0 B> 0` never occurs: B is entered from A, which leaves a 1 on its left).
- `py/defects.py`, `py/near_halt.py` (heuristic): defect counts at the left-end turns; neighbourhoods of B, C, F.

## What is open, next steps

Everything beyond the local moves. Possible routes: describe one zig-zag as a rule on the list of defect positions,
or search for a closed set of local patterns (a CTL with larger windows) that excludes `0 B> 0` and `0 F> 0`.

**Later**: no structure found in the first pass; this machine was set aside in favour of the more regular ones.

## Deciders tried (F11, 13 November 2026)

None closes. Each reaches a halting configuration in its abstraction, which says nothing about halting.

- n-gram CPS (`tools/c/ngramcps.c`), equal widths on both sides: a halting local configuration is reached with plain up to width 20, history 1 up to width 20, history 2 up to width 20, history 3 up to width 20, LRU history up to width 11 (larger widths ran out of the 150 s or 60 million configuration budget).
- n-gram CPS with every cell tagged by its position mod p: fails for p = 2 up to width 20, p = 3 up to width 20, p = 4 up to width 16, p = 6 up to width 20.
- n-gram CPS where each side also carries the state of a small automaton that has read that side from the far end (every automaton with up to 3 states on both sides, or 4 states on one side), with position mod 1..4 and widths 4, 6, 8: no closed set without a halt in all 120 parameter sets.
- Run-length windows (the K nearest runs of equal macro cells on each side, run lengths kept exactly below T and mod M above): fails for all 72 parameter sets (cells of 1 to 4 bits, K = 2, 4, 6, T = 2, 4, M = 1, 2, 4).
- Two-automaton closed tape language by SAT (a deterministic automaton reading each side inward, n states each, CaDiCaL): no solution for n = 2..8; n = 9 not finished in 150 s.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE/lean/check.sh
python3 holdouts/1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE/py/route.py        # rewrites lean/Route.lean
python3 holdouts/1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE/py/rules.py       # rewrites lean/Rules.lean
python3 holdouts/1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE/py/defects.py 1e7 40
python3 holdouts/1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE/py/near_halt.py 1e6
```
